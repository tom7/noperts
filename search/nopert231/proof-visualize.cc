// 4K images of the #231 proof over the view domain (the plane x + y + z = 1
// of the code triangles; a point p is the view direction p / |p|). Each
// image outlines the 153 code triangles.
//
//   --tube      identity tube: the certified radius rLower of the tube-tree
//               leaf at each view (per pixel, the minimum over the leaves
//               touching it), log scale.
//   --search5d  where the 5D search worked: leaf density per view (leaves per
//               unit area, log scale) from the journals, for --chart C (0..2)
//               or all charts.
//   --margin    first-order rigidity margin of #231's identity pose at each
//               view (rigidity-margin.h), log scale; the canyon is dark.
//
// Usage: proof-visualize.exe (--tube | --search5d | --margin) [--out FILE.png]
//          [--trees_dir trees_r2] [--bdd codebdd231.json] [--journals jobs]
//          [--chart C] [--zoom T] [--threads N] [--width 3840 --height 2160]
//   --zoom T: fit the image to code triangle T (e.g. 102, code 51.0: the canyon).
//   e.g. proof-visualize.exe --tube --out tube.png
//        proof-visualize.exe --search5d --chart 0 --out search_c0.png

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <format>
#include <limits>
#include <map>
#include <mutex>
#include <string>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "geom5d.h"
#include "image.h"
#include "nopert231.h"
#include "rigidity-margin.h"
#include "rows5d.h"
#include "threadutil.h"
#include "tubeatlas5d.h"

using vec3 = geom5d::vec3;
using vec2 = yocto::vec<double, 2>;

namespace {

// The view plane x + y + z = 1 in 2D coordinates, fitted to the image.
struct Frame {
  int width = 3840, height = 2160;
  vec3 e1 = yocto::normalize(vec3{1, -1, 0}), e2 = yocto::normalize(vec3{1, 1, -2});
  vec2 lo{1e9, 1e9}, hi{-1e9, -1e9};
  double scale = 1, ox = 0, oy = 0;
  // Leave room on the right for the color bar.
  static constexpr int kMargin = 80, kBar = 360;

  vec2 Plane(const vec3 &p) const { return {yocto::dot(p, e1), yocto::dot(p, e2)}; }
  void Fit(const std::vector<geom5d::TriangleD> &tris) {
    for (const auto &t : tris) {
      for (const vec3 &c : t.corners) {
        const vec2 q = Plane(c);
        lo = {std::min(lo.x, q.x), std::min(lo.y, q.y)};
        hi = {std::max(hi.x, q.x), std::max(hi.y, q.y)};
      }
    }
    const double w = width - 2 * kMargin - kBar, h = height - 2 * kMargin;
    scale = std::min(w / (hi.x - lo.x), h / (hi.y - lo.y));
    ox = kMargin + (w - scale * (hi.x - lo.x)) / 2;
    oy = kMargin + (h - scale * (hi.y - lo.y)) / 2;
  }
  vec2 Pixel(const vec3 &p) const {
    const vec2 q = Plane(p);
    return {ox + (q.x - lo.x) * scale, oy + (hi.y - q.y) * scale};
  }
  // The point of the view plane at pixel (x, y).
  vec3 Point(double x, double y) const {
    const double a = lo.x + (x - ox) / scale, b = hi.y - (y - oy) / scale;
    // p = c + a e1 + b e2 with c = (1,1,1)/3 (e1, e2 are orthogonal to it).
    return vec3{1.0 / 3, 1.0 / 3, 1.0 / 3} + e1 * a + e2 * b;
  }
};

// Calls f(px, py) for each pixel center inside triangle t, or for the pixel
// of its centroid if it covers none. Returns the number of pixels.
template <class F>
int RasterTriangle(const Frame &fr, const geom5d::TriangleD &t, const F &f) {
  vec2 p[3];
  for (int i = 0; i < 3; i++) p[i] = fr.Pixel(t.corners[i]);
  const int x0 = std::max(0, (int)std::floor(std::min({p[0].x, p[1].x, p[2].x})));
  const int x1 = std::min(fr.width - 1, (int)std::ceil(std::max({p[0].x, p[1].x, p[2].x})));
  const int y0 = std::max(0, (int)std::floor(std::min({p[0].y, p[1].y, p[2].y})));
  const int y1 = std::min(fr.height - 1, (int)std::ceil(std::max({p[0].y, p[1].y, p[2].y})));
  auto edge = [](const vec2 &a, const vec2 &b, double x, double y) {
    return (b.x - a.x) * (y - a.y) - (b.y - a.y) * (x - a.x);
  };
  const double area = edge(p[0], p[1], p[2].x, p[2].y);
  int n = 0;
  if (std::abs(area) > 1e-12) {
    for (int y = y0; y <= y1; y++) {
      for (int x = x0; x <= x1; x++) {
        const double cx = x + 0.5, cy = y + 0.5;
        const double w0 = edge(p[1], p[2], cx, cy) / area, w1 = edge(p[2], p[0], cx, cy) / area,
                     w2 = edge(p[0], p[1], cx, cy) / area;
        if (w0 >= 0 && w1 >= 0 && w2 >= 0) { f(x, y); n++; }
      }
    }
  }
  if (n == 0) {
    const int x = (int)((p[0].x + p[1].x + p[2].x) / 3), y = (int)((p[0].y + p[1].y + p[2].y) / 3);
    if (x >= 0 && y >= 0 && x < fr.width && y < fr.height) { f(x, y); n = 1; }
  }
  return n;
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

// Text at 4x size (the built-in font is small for 4K).
void BigText(ImageRGBA *img, int x, int y, uint32_t color, const std::string &s, int scale = 4) {
  ImageRGBA t(18 * (int)s.size() + 4, 36);
  t.Clear32(0x00000000);
  t.BlendText2x32(1, 1, color, s);
  img->BlendImage(x, y, t.ScaleBy(scale / 2));
}

// Paints values (log10, NaN = none) with a color bar labeled lo..hi.
ImageRGBA Render(const Frame &fr, const std::vector<double> &vals, double lo, double hi,
                 const std::vector<geom5d::TriangleD> &outlines, const std::string &title,
                 const std::string &unit) {
  ImageRGBA img(fr.width, fr.height);
  img.Clear32(0x101018FF);
  for (int y = 0; y < fr.height; y++) {
    for (int x = 0; x < fr.width; x++) {
      const double v = vals[y * fr.width + x];
      if (std::isfinite(v)) img.SetPixel32(x, y, Viridis((v - lo) / (hi - lo)));
    }
  }
  for (const auto &t : outlines) {
    for (int i = 0; i < 3; i++) {
      const vec2 a = fr.Pixel(t.corners[i]), b = fr.Pixel(t.corners[(i + 1) % 3]);
      img.BlendLineAA32(a.x, a.y, b.x, b.y, 0xFFFFFF60);
    }
  }
  // Color bar.
  const int bx = fr.width - Frame::kBar + 40, by = 260, bh = fr.height - 520, bw = 60;
  for (int i = 0; i < bh; i++) img.FillRect32(bx, by + i, bw, 1, Viridis(1.0 - (double)i / bh));
  for (int k = 0; k <= 4; k++) {
    const double v = hi - (hi - lo) * k / 4;
    BigText(&img, bx + bw + 16, by + bh * k / 4 - 18, 0xEEEEEEFF, std::format("1e{:.1f}", v));
  }
  BigText(&img, bx - 20, by - 90, 0xEEEEEEFF, unit);
  BigText(&img, Frame::kMargin, 20, 0xFFFFFFFF, title, 6);
  return img;
}

}  // namespace

int main(int argc, char **argv) {
  std::string mode, out, trees_dir = "trees_r2", bdd = "codebdd231.json", journals = "jobs";
  int chart = -1, threads = 60, zoom = -1;
  Frame fr;
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
    else if (a == "--zoom") zoom = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--width") fr.width = std::stoi(next());
    else if (a == "--height") fr.height = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(!mode.empty()) << "one of --tube, --search5d, --margin";
  if (out.empty()) out = mode + (mode == "search5d" && chart >= 0 ? std::format("_c{}", chart) : "") + ".png";

  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  std::vector<geom5d::TriangleD> code_tris;
  for (int t = 0; t < atlas.NumTriangles(); t++) code_tris.push_back(geom5d::ToDouble(atlas.Triangle(t)));
  // --zoom T fits the frame to code triangle T (others are still drawn).
  fr.Fit(zoom >= 0 ? std::vector<geom5d::TriangleD>{code_tris[zoom]} : code_tris);
  const size_t npix = (size_t)fr.width * fr.height;
  std::vector<double> vals(npix, std::numeric_limits<double>::quiet_NaN());
  std::mutex mu;
  ImageRGBA img(1, 1);

  if (mode == "tube") {
    // Per pixel, the minimum leaf radius (log10) over leaves touching it.
    std::vector<double> minr(npix, std::numeric_limits<double>::infinity());
    std::atomic<int64_t> leaves{0};
    ParallelComp(atlas.NumTriangles(), [&](int64_t t) {
      std::vector<std::string> stack = {""};
      std::vector<std::pair<int, double>> local;  // (pixel, log10 r)
      while (!stack.empty()) {
        const std::string path = stack.back();
        stack.pop_back();
        const auto r = atlas.Walk(t, path);
        if (r.depth < (int)path.size()) continue;  // past a leaf
        if (!r.leaf) {
          for (char c : std::string("0123")) stack.push_back(path + c);
          continue;
        }
        leaves++;
        const double lr = std::log10(std::max(1e-30, r.r_lower.ToDouble()));
        const auto tri = geom5d::SplitTrianglePath(atlas.Triangle(t), path);
        RasterTriangle(fr, geom5d::ToDouble(tri), [&](int x, int y) { local.push_back({y * fr.width + x, lr}); });
      }
      std::lock_guard<std::mutex> l(mu);
      for (const auto &[p, lr] : local) minr[p] = std::min(minr[p], lr);
    }, threads);
    for (size_t i = 0; i < npix; i++) if (std::isfinite(minr[i])) vals[i] = minr[i];
    Print("{} tube leaves\n", leaves.load());
    img = Render(fr, vals, -5.0, -2.0, code_tris,
                 "Nopert #231: identity tube radius (certified rLower of the tube-tree leaf)",
                 "radius");
  } else if (mode == "search5d") {
    // Leaf density: each leaf spreads weight 1 over the pixels of its view
    // triangle; then leaves per unit plane area.
    std::vector<double> dens(npix, 0.0);
    std::vector<int> charts = chart >= 0 ? std::vector<int>{chart} : std::vector<int>{0, 1, 2};
    std::atomic<int64_t> total{0};
    std::vector<std::pair<int, int>> jobs;
    for (int c : charts) for (int t = 0; t < atlas.NumTriangles(); t++) jobs.push_back({c, t});
    ParallelComp(jobs.size(), [&](int64_t k) {
      const auto [c, t] = jobs[k];
      const auto j = rows5d::ReadJournal(std::format("{}/c{}/t{}.journal", journals, c, t));
      std::map<std::string, int64_t> per_view;
      for (const auto &r : j.leaves) per_view[rows5d::ViewPath(r.path)]++;
      total += j.leaves.size();
      std::vector<std::pair<int, double>> local;
      const geom5d::TriangleD root = geom5d::ToDouble(atlas.Triangle(t));
      for (const auto &[view, n] : per_view) {
        geom5d::TriangleD tri = root;
        for (char d : view) tri = geom5d::SplitTriangle(tri, d - '0');
        std::vector<int> pix;
        RasterTriangle(fr, tri, [&](int x, int y) { pix.push_back(y * fr.width + x); });
        for (int p : pix) local.push_back({p, (double)n / pix.size()});
      }
      std::lock_guard<std::mutex> l(mu);
      for (const auto &[p, w] : local) dens[p] += w;
    }, threads);
    // Per unit plane area: one pixel is 1/scale^2.
    const double pixel_area = 1.0 / (fr.scale * fr.scale);
    for (size_t i = 0; i < npix; i++) if (dens[i] > 0) vals[i] = std::log10(dens[i] / pixel_area);
    Print("{} leaves\n", total.load());
    img = Render(fr, vals, 3.0, 11.0, code_tris,
                 std::format("Nopert #231: 5D search leaves per unit view area ({})",
                             chart >= 0 ? std::format("chart {}", chart) : std::string("charts 0-2")),
                 "leaves/area");
  } else {
    std::vector<rigidity::vec3> verts;
    for (int i = 0; i < NUM_VERTICES; i++) verts.push_back({VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]});
    // Only inside the code triangles (the view domain).
    std::vector<char> inside(npix, 0);
    for (const auto &t : code_tris) RasterTriangle(fr, t, [&](int x, int y) { inside[y * fr.width + x] = 1; });
    ParallelComp(fr.height, [&](int64_t y) {
      for (int x = 0; x < fr.width; x++) {
        if (!inside[y * fr.width + x]) continue;
        const vec3 p = fr.Point(x + 0.5, y + 0.5);
        const double m = rigidity::FirstOrderMargin(verts, yocto::normalize(p), false).m;
        vals[y * fr.width + x] = std::log10(std::max(1e-6, m));
      }
    }, threads);
    img = Render(fr, vals, -4.0, -0.5, code_tris,
                 "Nopert #231: first-order rigidity margin of the identity pose", "margin");
  }
  CHECK(img.Save(out)) << out;
  (void)zoom;
  Print("wrote {}\n", out);
  return 0;
}
