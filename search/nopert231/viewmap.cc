// viewmap: the proof's data over all view directions, for rendering (e.g. on
// the solid in Blender). Not used by the proof.
//
// A quantity is computed over the proof's view triangle T (the union of the
// code triangles, on the plane x + y + z = 1; a point p is the view p / |p|)
// on a G x G grid, then mapped to every view direction d by the symmetry
// reduction the proof uses: d and -d, and their images under the solid's
// rotations (found numerically from its vertices), have the same shadows up
// to congruence, and one of them lies in T.
//
//   --margin    first-order rigidity margin of the identity pose
//               (rigidity-margin.h), log scale: the canyon is dark.
//   --search5d  5D search leaves per unit view area (from the journals; one
//               --chart C or all), log scale: where the search worked.
//   --tube      the identity tube's certified radius (the tube-tree leaf at
//               each view; per grid cell, the minimum), log scale.
//
// Outputs (BASE from --out):
//   BASE.png         --equirect W: a W x W/2 equirectangular image (Blender's
//                    Environment Texture convention, as codebdd --texture;
//                    blender_code_texture.py applies it).
//   BASE.obj/.mtl,   --udim S: the solid, one S x S UDIM tile per triangle
//   BASE.<UDIM>.png  (Blender: import the OBJ; the material's image is
//                    BASE.<UDIM>.png as UDIM tiles). Each texel takes the
//                    value of its direction from the origin.
//   BASE_colorbar.png  the color scale (log10; --range LO HI, default the
//                    1% and 99.5% quantiles over T).
//   BASE_views.txt   the most extreme views (smallest margin or tube radius,
//                    densest search), each with the object rotation that
//                    turns it toward +z, i.e. toward a camera on the +z axis
//                    looking down, which then sees the solid's shadow along
//                    that view.
// Code boundaries are darkened (--no_outline to omit).
//
// Memory is about 12 G^2 + 4 W^2/2 + 8 S^2 bytes, plus the search journals
// for --search5d (one triangle at a time): e.g. --grid 8192 --equirect 32768
// --udim 8192 needs about 3.5 GB. Time is dominated by --margin's grid (six
// small LPs per cell inside T).
//
// Usage: viewmap.exe (--margin | --search5d | --tube) [--out BASE]
//          [--trees_dir work/trees_r2] [--bdd codebdd.json] [--journals work/jobs]
//          [--chart C] [--grid 2048] [--equirect 4096] [--udim 1024]
//          [--range LO HI] [--views 8] [--threads N] [--no_outline]

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <format>
#include <limits>
#include <map>
#include <mutex>
#include <numbers>
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "geom5d.h"
#include "image.h"
#include "model.h"
#include "rigidity-margin.h"
#include "rows5d.h"
#include "threadutil.h"
#include "tubeatlas5d.h"
#include "util.h"

using vec3 = yocto::vec<double, 3>;
using vec2 = yocto::vec<double, 2>;
using mat3 = yocto::mat<double, 3>;

namespace {

constexpr double kNaN = std::numeric_limits<double>::quiet_NaN();

// The grid over T: the plane x + y + z = 1 in 2D coordinates.
struct Grid {
  int n = 2048;  // cells per side of the bounding square
  vec3 e1 = yocto::normalize(vec3{1, -1, 0}), e2 = yocto::normalize(vec3{1, 1, -2});
  vec2 lo{1e9, 1e9};
  double cell = 1;  // plane units per cell
  std::vector<float> val;      // log10 of the quantity; NaN outside T
  std::vector<int16_t> code;   // code id; -1 outside T

  vec2 Plane(const vec3 &p) const { return {yocto::dot(p, e1), yocto::dot(p, e2)}; }
  void Fit(const std::vector<geom5d::TriangleD> &tris) {
    vec2 hi{-1e9, -1e9};
    for (const auto &t : tris) {
      for (const vec3 &c : t.corners) {
        const vec2 q = Plane(c);
        lo = {std::min(lo.x, q.x), std::min(lo.y, q.y)};
        hi = {std::max(hi.x, q.x), std::max(hi.y, q.y)};
      }
    }
    cell = std::max(hi.x - lo.x, hi.y - lo.y) / n;
    val.assign((size_t)n * n, kNaN);
    code.assign((size_t)n * n, -1);
  }
  // The point of the plane at the center of cell (x, y).
  vec3 Point(int x, int y) const {
    const double a = lo.x + (x + 0.5) * cell, b = lo.y + (y + 0.5) * cell;
    return vec3{1.0 / 3, 1.0 / 3, 1.0 / 3} + e1 * a + e2 * b;
  }
  // The cell of a plane point (may be out of range).
  std::pair<int, int> Cell(const vec3 &p) const {
    const vec2 q = Plane(p);
    return {(int)std::floor((q.x - lo.x) / cell), (int)std::floor((q.y - lo.y) / cell)};
  }
  size_t Index(int x, int y) const { return (size_t)y * n + x; }
};

// Calls f(x, y) for each cell whose center is inside triangle t, or the cell
// of its centroid if there is none. Returns the number of cells.
template <class F>
int RasterTriangle(const Grid &g, const geom5d::TriangleD &t, const F &f) {
  vec2 p[3];
  for (int i = 0; i < 3; i++) {
    const vec2 q = g.Plane(t.corners[i] / (t.corners[i].x + t.corners[i].y + t.corners[i].z));
    p[i] = {(q.x - g.lo.x) / g.cell, (q.y - g.lo.y) / g.cell};
  }
  const int x0 = std::max(0, (int)std::floor(std::min({p[0].x, p[1].x, p[2].x})));
  const int x1 = std::min(g.n - 1, (int)std::ceil(std::max({p[0].x, p[1].x, p[2].x})));
  const int y0 = std::max(0, (int)std::floor(std::min({p[0].y, p[1].y, p[2].y})));
  const int y1 = std::min(g.n - 1, (int)std::ceil(std::max({p[0].y, p[1].y, p[2].y})));
  auto edge = [](const vec2 &a, const vec2 &b, double x, double y) {
    return (b.x - a.x) * (y - a.y) - (b.y - a.y) * (x - a.x);
  };
  const double area = edge(p[0], p[1], p[2].x, p[2].y);
  int count = 0;
  if (std::abs(area) > 1e-18) {
    for (int y = y0; y <= y1; y++) {
      for (int x = x0; x <= x1; x++) {
        const double cx = x + 0.5, cy = y + 0.5;
        const double w0 = edge(p[1], p[2], cx, cy) / area, w1 = edge(p[2], p[0], cx, cy) / area,
                     w2 = edge(p[0], p[1], cx, cy) / area;
        if (w0 >= 0 && w1 >= 0 && w2 >= 0) { f(x, y); count++; }
      }
    }
  }
  if (count == 0) {
    const int x = (int)((p[0].x + p[1].x + p[2].x) / 3), y = (int)((p[0].y + p[1].y + p[2].y) / 3);
    if (x >= 0 && y >= 0 && x < g.n && y < g.n) { f(x, y); count = 1; }
  }
  return count;
}

// A perceptual (viridis-like) colormap, t in [0, 1].
uint32_t Viridis(double t) {
  static const double c[][3] = {{68, 1, 84}, {72, 40, 120}, {62, 74, 137}, {49, 104, 142},
                                {38, 130, 142}, {31, 158, 137}, {53, 183, 121}, {109, 205, 89},
                                {180, 222, 44}, {253, 231, 37}};
  t = std::clamp(t, 0.0, 1.0) * 9;
  const int i = std::min(8, (int)t);
  const double f = t - i;
  auto ch = [&](int k) { return (uint32_t)std::lround(c[i][k] + f * (c[i + 1][k] - c[i][k])); };
  return (ch(0) << 24) | (ch(1) << 16) | (ch(2) << 8) | 0xFF;
}

// The solid's distinct vertices (a point may be listed in several slots).
std::vector<vec3> DistinctVertices() {
  std::vector<vec3> pts;
  for (int i = 0; i < NUM_VERTICES; i++) {
    const vec3 p = Vertex(i);
    bool dup = false;
    for (const vec3 &q : pts) dup = dup || yocto::distance(p, q) < 1e-12;
    if (!dup) pts.push_back(p);
  }
  return pts;
}

// The orthogonal maps of the point set: those taking a frame of three points
// to a congruent triple and the set onto itself.
std::vector<mat3> Symmetries(const std::vector<vec3> &pts) {
  const int n = pts.size();
  int b = 1;
  for (int j = 1; j < n; j++) if (yocto::distance(pts[j], pts[0]) < yocto::distance(pts[b], pts[0])) b = j;
  int c = -1;
  for (int j = 1; j < n; j++) {
    if (j == b || std::abs(yocto::dot(pts[0], yocto::cross(pts[b], pts[j]))) < 1e-3) continue;
    if (c < 0 || yocto::distance(pts[j], pts[0]) < yocto::distance(pts[c], pts[0])) c = j;
  }
  CHECK(c >= 0);
  const mat3 Xinv = yocto::inverse(mat3{pts[0], pts[b], pts[c]});
  auto close = [](double x, double y) { return std::abs(x - y) < 1e-9; };
  std::vector<mat3> out;
  for (int a2 = 0; a2 < n; a2++) {
    if (!close(yocto::length(pts[a2]), yocto::length(pts[0]))) continue;
    for (int b2 = 0; b2 < n; b2++) {
      if (!close(yocto::length(pts[b2]), yocto::length(pts[b])) ||
          !close(yocto::distance(pts[a2], pts[b2]), yocto::distance(pts[0], pts[b]))) continue;
      for (int c2 = 0; c2 < n; c2++) {
        if (!close(yocto::length(pts[c2]), yocto::length(pts[c])) ||
            !close(yocto::distance(pts[a2], pts[c2]), yocto::distance(pts[0], pts[c])) ||
            !close(yocto::distance(pts[b2], pts[c2]), yocto::distance(pts[b], pts[c]))) continue;
        const mat3 M = mat3{pts[a2], pts[b2], pts[c2]} * Xinv;
        bool ok = true;
        for (int i = 0; i < n && ok; i++) {
          bool hit = false;
          for (int j = 0; j < n && !hit; j++) hit = yocto::distance(M * pts[i], pts[j]) < 1e-9;
          ok = hit;
        }
        if (ok) out.push_back(M);
      }
    }
  }
  return out;
}

// Maps view directions into T: d -> s g d for a symmetry g and s = +-1.
struct Reducer {
  std::vector<mat3> maps;  // s g, both signs
  std::vector<vec3> pull;  // (s g)^T c: <s g d, c> = <d, pull>
  mat3 corners_inv;        // barycentric coordinates w.r.t. T's corners
  Reducer(const std::vector<mat3> &syms, const std::array<vec3, 3> &T) {
    const vec3 c = yocto::normalize(T[0] + T[1] + T[2]);
    for (const mat3 &g : syms) {
      for (double s : {1.0, -1.0}) {
        maps.push_back(g * s);
        pull.push_back(yocto::transpose(g * s) * c);
      }
    }
    corners_inv = yocto::inverse(mat3{T[0], T[1], T[2]});
  }
  double MinBary(const vec3 &e) const {
    const vec3 w = corners_inv * e;
    return std::min({w.x, w.y, w.z});
  }
  // The image of d in T (the plane point), trying the image nearest T's
  // center first (for a group whose chamber is T's Dirichlet cell, it is in T).
  vec3 Reduce(const vec3 &d) const {
    int best = 0;
    for (int k = 1; k < (int)maps.size(); k++) {
      if (yocto::dot(d, pull[k]) > yocto::dot(d, pull[best])) best = k;
    }
    vec3 e = maps[best] * d;
    if (MinBary(e) < -1e-12) {
      double bm = -1e30;
      for (const mat3 &M : maps) {
        const vec3 f = M * d;
        const double m = MinBary(f);
        if (m > bm) { bm = m; e = f; }
        if (m >= -1e-12) break;
      }
    }
    return e / (e.x + e.y + e.z);
  }
};

// The convex hull corners of the code triangles' union (a triangle).
std::array<vec3, 3> ViewTriangle(const std::vector<geom5d::TriangleD> &tris) {
  std::vector<vec3> pts;
  for (const auto &t : tris) for (const vec3 &c : t.corners) pts.push_back(c / (c.x + c.y + c.z));
  // Farthest pair, then the point farthest from their line.
  int a = 0, b = 0;
  double best = -1;
  for (size_t i = 0; i < pts.size(); i++) {
    for (size_t j = i + 1; j < pts.size(); j++) {
      if (yocto::distance(pts[i], pts[j]) > best) { best = yocto::distance(pts[i], pts[j]); a = i; b = j; }
    }
  }
  int c = 0;
  best = -1;
  for (size_t k = 0; k < pts.size(); k++) {
    const double h = yocto::length(yocto::cross(pts[b] - pts[a], pts[k] - pts[a]));
    if (h > best) { best = h; c = k; }
  }
  return {pts[a], pts[b], pts[c]};
}

// The solid's faces as triangles (double precision; facets of the distinct
// vertices, each fanned in counterclockwise order seen from outside).
std::vector<std::array<vec3, 3>> SolidTriangles(const std::vector<vec3> &pts) {
  const int n = pts.size();
  std::vector<std::vector<int>> facets;
  std::vector<vec3> normals;
  for (int a = 0; a < n; a++) {
    for (int b = a + 1; b < n; b++) {
      for (int c = b + 1; c < n; c++) {
        vec3 nv = yocto::cross(pts[b] - pts[a], pts[c] - pts[a]);
        if (yocto::length(nv) < 1e-9) continue;
        nv = yocto::normalize(nv);
        bool pos = false, neg = false;
        std::vector<int> on;
        for (int k = 0; k < n; k++) {
          const double s = yocto::dot(nv, pts[k] - pts[a]);
          if (s > 1e-9) pos = true;
          else if (s < -1e-9) neg = true;
          else on.push_back(k);
        }
        if (pos && neg) continue;
        if (std::find(facets.begin(), facets.end(), on) != facets.end()) continue;
        facets.push_back(on);
        normals.push_back(pos ? -nv : nv);
      }
    }
  }
  std::vector<std::array<vec3, 3>> tris;
  for (size_t f = 0; f < facets.size(); f++) {
    std::vector<int> fv = facets[f];
    vec3 center{0, 0, 0};
    for (int v : fv) center += pts[v];
    center /= (double)fv.size();
    const vec3 e1 = yocto::normalize(pts[fv[0]] - center), e2 = yocto::cross(normals[f], e1);
    auto ang = [&](int v) { return std::atan2(yocto::dot(pts[v] - center, e2), yocto::dot(pts[v] - center, e1)); };
    std::sort(fv.begin(), fv.end(), [&](int x, int y) { return ang(x) < ang(y); });
    for (size_t t = 1; t + 1 < fv.size(); t++) tris.push_back({pts[fv[0]], pts[fv[t]], pts[fv[t + 1]]});
  }
  return tris;
}

// The rotation taking unit vector u to +z (Rodrigues), as a matrix.
mat3 RotationToZ(const vec3 &u) {
  const vec3 z{0, 0, 1};
  const vec3 axis = yocto::cross(u, z);
  const double s = yocto::length(axis), c = yocto::dot(u, z);
  if (s < 1e-12) {
    return c > 0 ? mat3{{1, 0, 0}, {0, 1, 0}, {0, 0, 1}} : mat3{{1, 0, 0}, {0, -1, 0}, {0, 0, -1}};
  }
  const vec3 k = axis / s;
  const mat3 K = {{0, k.z, -k.y}, {-k.z, 0, k.x}, {k.y, -k.x, 0}};  // columns: K v = k x v
  const mat3 I = {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}};
  return I + K * s + K * K * (1 - c);
}

}  // namespace

int main(int argc, char **argv) {
  std::string mode, out, trees_dir = "trees_r2", bdd = "codebdd.json", journals = "jobs";
  int chart = -1, threads = (int)std::thread::hardware_concurrency(), equirect = 4096, udim = 1024;
  int num_views = 8;
  bool outline = true;
  double range_lo = kNaN, range_hi = kNaN;
  Grid grid;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--tube" || a == "--search5d" || a == "--margin") mode = a.substr(2);
    else if (a == "--out") out = next();
    else if (a == "--trees_dir") trees_dir = next();
    else if (a == "--bdd") bdd = next();
    else if (a == "--journals") journals = next();
    else if (a == "--chart") chart = std::stoi(next());
    else if (a == "--grid") grid.n = std::stoi(next());
    else if (a == "--equirect") equirect = std::stoi(next());
    else if (a == "--udim") udim = std::stoi(next());
    else if (a == "--views") num_views = std::stoi(next());
    else if (a == "--range") { range_lo = std::stod(next()); range_hi = std::stod(next()); }
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--no_outline") outline = false;
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(!mode.empty()) << "one of --margin, --search5d, --tube";
  if (out.empty()) out = "viewmap_" + mode + (mode == "search5d" && chart >= 0 ? std::format("_c{}", chart) : "");

  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  std::vector<geom5d::TriangleD> code_tris;
  for (int t = 0; t < atlas.NumTriangles(); t++) code_tris.push_back(geom5d::ToDouble(atlas.Triangle(t)));
  grid.Fit(code_tris);
  for (int t = 0; t < atlas.NumTriangles(); t++) {
    const int16_t code = atlas.CodeAndTriangle(t).first;
    RasterTriangle(grid, code_tris[t], [&](int x, int y) { grid.code[grid.Index(x, y)] = code; });
  }
  const std::vector<vec3> pts = DistinctVertices();
  const std::vector<mat3> syms = Symmetries(pts);
  const Reducer reducer(syms, ViewTriangle(code_tris));
  Print("{} code triangles, {} distinct vertices, {} symmetries; grid {}^2\n", code_tris.size(),
        pts.size(), syms.size(), grid.n);

  // The quantity on the grid.
  std::mutex mu;
  const size_t ncells = (size_t)grid.n * grid.n;
  if (mode == "margin") {
    std::vector<rigidity::vec3> verts(pts.begin(), pts.end());
    std::atomic<int64_t> done{0};
    ParallelComp(grid.n, [&](int64_t y) {
      for (int x = 0; x < grid.n; x++) {
        const size_t i = grid.Index(x, y);
        if (grid.code[i] < 0) continue;
        const double m = rigidity::FirstOrderMargin(verts, yocto::normalize(grid.Point(x, y)), false).m;
        grid.val[i] = (float)std::log10(std::max(1e-9, m));
      }
      if (++done % 256 == 0) Print("  margin: {}/{} rows\n", done.load(), grid.n);
    }, threads);
  } else if (mode == "tube") {
    std::vector<float> minr(ncells, std::numeric_limits<float>::infinity());
    ParallelComp(atlas.NumTriangles(), [&](int64_t t) {
      std::vector<std::string> stack = {""};
      std::vector<std::pair<size_t, float>> local;
      while (!stack.empty()) {
        const std::string path = stack.back();
        stack.pop_back();
        const auto r = atlas.Walk(t, path);
        if (r.depth < (int)path.size()) continue;
        if (!r.leaf) {
          for (char c : std::string("0123")) stack.push_back(path + c);
          continue;
        }
        const float lr = (float)std::log10(std::max(1e-30, r.r_lower.ToDouble()));
        const auto tri = geom5d::ToDouble(geom5d::SplitTrianglePath(atlas.Triangle(t), path));
        RasterTriangle(grid, tri, [&](int x, int y) { local.push_back({grid.Index(x, y), lr}); });
      }
      std::lock_guard<std::mutex> l(mu);
      for (const auto &[p, lr] : local) minr[p] = std::min(minr[p], lr);
    }, threads);
    for (size_t i = 0; i < ncells; i++) if (std::isfinite(minr[i])) grid.val[i] = minr[i];
  } else {
    std::vector<double> dens(ncells, 0.0);
    std::vector<int> charts = chart >= 0 ? std::vector<int>{chart} : std::vector<int>{0, 1, 2};
    std::vector<std::pair<int, int>> jobs;
    for (int c : charts) for (int t = 0; t < atlas.NumTriangles(); t++) jobs.push_back({c, t});
    std::atomic<int64_t> total{0};
    ParallelComp(jobs.size(), [&](int64_t k) {
      const auto [c, t] = jobs[k];
      const auto j = rows5d::ReadJournal(std::format("{}/c{}/t{}.journal", journals, c, t));
      std::map<std::string, int64_t> per_view;
      for (const auto &r : j.leaves) per_view[rows5d::ViewPath(r.path)]++;
      total += j.leaves.size();
      std::vector<std::pair<size_t, double>> local;
      const geom5d::TriangleD root = code_tris[t];
      for (const auto &[view, n] : per_view) {
        geom5d::TriangleD tri = root;
        for (char d : view) tri = geom5d::SplitTriangle(tri, d - '0');
        std::vector<size_t> cells;
        RasterTriangle(grid, tri, [&](int x, int y) { cells.push_back(grid.Index(x, y)); });
        for (size_t p : cells) local.push_back({p, (double)n / cells.size()});
      }
      std::lock_guard<std::mutex> l(mu);
      for (const auto &[p, w] : local) dens[p] += w;
    }, threads);
    // Per unit plane area.
    const double cell_area = grid.cell * grid.cell;
    for (size_t i = 0; i < ncells; i++) if (dens[i] > 0) grid.val[i] = (float)std::log10(dens[i] / cell_area);
    Print("{} search leaves\n", total.load());
    CHECK(total.load() > 0) << "no journals in " << journals;
  }

  // The color range (log10): by default the 1% and 99.5% quantiles over T.
  if (!std::isfinite(range_lo)) {
    std::vector<float> vs;
    for (float v : grid.val) if (std::isfinite(v)) vs.push_back(v);
    CHECK(!vs.empty());
    std::sort(vs.begin(), vs.end());
    range_lo = vs[vs.size() / 100];
    range_hi = vs[vs.size() - 1 - vs.size() / 200];
    if (range_hi <= range_lo) range_hi = range_lo + 1;
  }
  Print("color range: 10^{:.3f} .. 10^{:.3f}\n", range_lo, range_hi);
  {
    // A color bar, low (left) to high (right), labeled with the range.
    ImageRGBA bar(1024, 96);
    bar.Clear32(0x000000FF);
    for (int x = 0; x < 1024; x++) bar.FillRect32(x, 0, 1, 64, Viridis(x / 1023.0));
    bar.BlendText2x32(4, 72, 0xFFFFFFFF, std::format("10^{:.2f}", range_lo));
    const std::string hi = std::format("10^{:.2f}", range_hi);
    bar.BlendText2x32(1024 - 18 * (int)hi.size() - 4, 72, 0xFFFFFFFF, hi);
    const std::string name = mode == "margin" ? "first-order margin" : mode == "tube" ? "tube radius"
                                                                    : "search leaves per unit view area";
    bar.BlendText2x32(512 - 9 * (int)name.size(), 72, 0xFFFFFFFF, name);
    CHECK(bar.Save(out + "_colorbar.png"));
  }

  // A view's color: its grid cell in T (the nearest valued cell if its own
  // has none, at T's boundary), darkened on code boundaries.
  auto Color = [&](const vec3 &d) -> uint32_t {
    const vec3 p = reducer.Reduce(yocto::normalize(d));
    auto [x, y] = grid.Cell(p);
    x = std::clamp(x, 0, grid.n - 1);
    y = std::clamp(y, 0, grid.n - 1);
    float v = grid.val[grid.Index(x, y)];
    int cx = x, cy = y;
    for (int r = 1; !std::isfinite(v) && r < 8; r++) {
      for (int dy = -r; dy <= r && !std::isfinite(v); dy++) {
        for (int dx = -r; dx <= r && !std::isfinite(v); dx++) {
          const int xx = x + dx, yy = y + dy;
          if (xx < 0 || yy < 0 || xx >= grid.n || yy >= grid.n) continue;
          v = grid.val[grid.Index(xx, yy)];
          cx = xx;
          cy = yy;
        }
      }
    }
    if (!std::isfinite(v)) return 0x000000FF;
    uint32_t rgba = Viridis((v - range_lo) / (range_hi - range_lo));
    if (outline) {
      const int16_t c0 = grid.code[grid.Index(cx, cy)];
      bool edge = false;
      for (const auto &[dx, dy] : {std::pair{1, 0}, {0, 1}, {-1, 0}, {0, -1}}) {
        const int xx = cx + dx, yy = cy + dy;
        if (xx < 0 || yy < 0 || xx >= grid.n || yy >= grid.n) continue;
        const int16_t c1 = grid.code[grid.Index(xx, yy)];
        edge = edge || (c1 >= 0 && c1 != c0);
      }
      if (edge) {
        rgba = ((((rgba >> 24) & 0xFF) * 3 / 5) << 24) | ((((rgba >> 16) & 0xFF) * 3 / 5) << 16) |
               ((((rgba >> 8) & 0xFF) * 3 / 5) << 8) | 0xFF;
      }
    }
    return rgba;
  };

  if (equirect > 0) {
    const int W = equirect, H = equirect / 2;
    ImageRGBA img(W, H);
    ParallelComp(H, [&](int64_t row) {
      for (int col = 0; col < W; col++) {
        const double u = (col + 0.5) / W, v = 1.0 - (row + 0.5) / H;
        const double az = (0.5 - u) * 2.0 * std::numbers::pi, el = (v - 0.5) * std::numbers::pi;
        img.SetPixel32(col, row, Color(vec3{std::cos(el) * std::cos(az), std::cos(el) * std::sin(az),
                                            std::sin(el)}));
      }
    }, threads);
    CHECK(img.Save(out + ".png")) << out << ".png";
    Print("wrote {}.png ({}x{})\n", out, W, H);
  }

  if (udim > 0) {
    // One tile per triangle: corner A at the tile's top left, B top right, C
    // bottom left; texels past the hypotenuse extrapolate (no seams).
    const auto tris = SolidTriangles(pts);
    CHECK(tris.size() < 9000);
    std::string obj = std::format("mtllib {}.mtl\n", Util::FileOf(out));
    for (const auto &t : tris) for (const vec3 &p : t) obj += std::format("v {:.17g} {:.17g} {:.17g}\n", p.x, p.y, p.z);
    for (size_t i = 0; i < tris.size(); i++) {
      const int U = i % 10, V = i / 10;
      obj += std::format("vt {} {}\nvt {} {}\nvt {} {}\n", U, V + 1, U + 1, V + 1, U, V);
    }
    obj += "usemtl codes\ns off\n";
    for (size_t i = 0; i < tris.size(); i++) {
      const int k = 3 * i + 1;
      obj += std::format("f {}/{} {}/{} {}/{}\n", k, k, k + 1, k + 1, k + 2, k + 2);
    }
    Util::WriteFile(out + ".obj", obj);
    Util::WriteFile(out + ".mtl", std::format("newmtl codes\n  Ka 1 1 1\n  Kd 1 1 1\n  Ks 0 0 0\n  Ns 10\n"
                                              "  d 1\n  illum 1\n  map_Kd {}.<UDIM>.png\n", Util::FileOf(out)));
    for (size_t i = 0; i < tris.size(); i++) {
      const auto &[A, B, C] = tris[i];
      ImageRGBA tile(udim, udim);
      ParallelComp(udim, [&](int64_t y) {
        for (int x = 0; x < udim; x++) {
          const double s = (x + 0.5) / udim, t = (y + 0.5) / udim;
          tile.SetPixel32(x, y, Color(A + (B - A) * s + (C - A) * t));
        }
      }, threads);
      CHECK(tile.Save(std::format("{}.{}.png", out, 1001 + i)));
    }
    Print("wrote {}.obj, {}.mtl and {} UDIM tiles {}.1001.png.. ({}^2)\n", out, out, tris.size(), out, udim);
  }

  // The most extreme views: grid cells that are local extrema (minima of the
  // margin or tube radius, maxima of the search density), at least 1% of T
  // apart.
  {
    const bool want_min = mode != "search5d";
    std::vector<std::pair<float, size_t>> cand;
    for (int y = 1; y + 1 < grid.n; y++) {
      for (int x = 1; x + 1 < grid.n; x++) {
        const float v = grid.val[grid.Index(x, y)];
        if (!std::isfinite(v)) continue;
        bool ext = true;
        for (int dy = -1; dy <= 1 && ext; dy++) {
          for (int dx = -1; dx <= 1 && ext; dx++) {
            const float w = grid.val[grid.Index(x + dx, y + dy)];
            if ((dx || dy) && std::isfinite(w)) ext = want_min ? v <= w : v >= w;
          }
        }
        if (ext) cand.push_back({want_min ? v : -v, grid.Index(x, y)});
      }
    }
    std::sort(cand.begin(), cand.end());
    std::vector<vec3> picked;
    std::string txt = std::format(
        "# viewmap --{}: the {} most extreme views in the proof's view triangle (local {} of\n"
        "# log10 value on the grid). A view u is shown by rotating the object by R (u -> +z):\n"
        "# a camera on the +z axis looking down (-z) then sees the shadow along u. Blender:\n"
        "# object.rotation_mode = 'QUATERNION'; object.rotation_quaternion = (w, x, y, z).\n"
        "# rank  log10  view u (x y z)  quaternion (w x y z)  euler XYZ (degrees)\n",
        mode, num_views, want_min ? "minima" : "maxima");
    for (const auto &[key, idx] : cand) {
      if ((int)picked.size() >= num_views) break;
      const int x = idx % grid.n, y = idx / grid.n;
      vec3 u = yocto::normalize(grid.Point(x, y));
      double value = grid.val[idx];
      if (mode == "margin") {
        std::vector<rigidity::vec3> verts(pts.begin(), pts.end());
        const auto [m, ur] = rigidity::RefineView(verts, u);
        if (m > 0) { u = yocto::normalize(ur); value = std::log10(m); }
      }
      bool near = false;
      for (const vec3 &q : picked) near = near || yocto::distance(q, u) < 0.05 * grid.n * grid.cell;
      if (near) continue;
      picked.push_back(u);
      const mat3 R = RotationToZ(u);
      // Quaternion from R (columns R.x, R.y, R.z; entry (r, c) = R[c][r]).
      const double m00 = R.x.x, m11 = R.y.y, m22 = R.z.z;
      const double qw = std::sqrt(std::max(0.0, 1 + m00 + m11 + m22)) / 2;
      const double qx = std::copysign(std::sqrt(std::max(0.0, 1 + m00 - m11 - m22)) / 2, R.y.z - R.z.y);
      const double qy = std::copysign(std::sqrt(std::max(0.0, 1 - m00 + m11 - m22)) / 2, R.z.x - R.x.z);
      const double qz = std::copysign(std::sqrt(std::max(0.0, 1 - m00 - m11 + m22)) / 2, R.x.y - R.y.x);
      // Blender XYZ Euler: R = Rz Ry Rx.
      const double ey = std::asin(std::clamp(-R.x.z, -1.0, 1.0));
      const double ex = std::atan2(R.y.z, R.z.z), ez = std::atan2(R.x.y, R.x.x);
      const double deg = 180.0 / std::numbers::pi;
      txt += std::format("{:4}  {:8.4f}  {:+.9f} {:+.9f} {:+.9f}  {:+.9f} {:+.9f} {:+.9f} {:+.9f}  {:.4f} {:.4f} {:.4f}\n",
                         picked.size(), value, u.x, u.y, u.z, qw, qx, qy, qz, ex * deg, ey * deg, ez * deg);
    }
    Util::WriteFile(out + "_views.txt", txt);
    Print("wrote {}_views.txt\n", out);
  }
  return 0;
}
