// tieviz: pictures of the deltoidal hexecontahedron's special poses, for
// video (4K PNG stills and lossless PNG .mov at 60 Hz). Not used by the
// proof. See tieviz.txt for what the pictures show.
//
// A pose is an outer view u and a rotation R (axis, angle) of the inner copy;
// the inner shadow is translated optimally (by central symmetry the best
// translation is 0). The frame shows the outer shadow (filled), the inner
// shadow (translucent amber, white outline) and in red any part of it outside
// the outer shadow; on the right, three insets zoomed uniformly around the
// places where the inner shadow comes closest to (or touches) the outer
// boundary, each marked on the whole shadow.
//
// Modes:
//   --still OUT.png --view x,y,z --axis x,y,z --theta T [--eta E]
//   --tie OUT.png --b B [--a A]: the pinning tie M(u) = sigma_u sigma_x for
//        x = (cos 18, sin 18, 2)/sqrt5 and u = x + a e1 + b e2
//   --wedge OUT.mov [--seconds 12]: u sweeps the wedge's center line from x
//        outward (b from 0.002 to 0.2) with R = M(u) (always an exact tie)
//   --poses FILE --out OUT.mov: one frame per line "eta ux uy uz ax ay az theta"
//   --mirror OUT.png [--eps E]: the 2-fold mirror tie at u = u0 + eps e2
//        (inner shadow = outer shadow)
//   --obj PREFIX (with --still/--tie): also PREFIX_outer.obj, PREFIX_inner.obj
//        (inner = R K) and PREFIX_view.txt, for Blender
// Common: [--width 3840] [--height 2160] [--zoom Z (inset pixels per unit)]
//         [--model dh_model.txt] (vertices and faces)
//
// --eta E scales the twelve 5-fold vertices by (1 + E) (E = 1/1000 makes the
// DH Rupert; dh_boundary.py).

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <format>
#include <fstream>
#include <numbers>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "geom/hull-2d.h"
#include "image.h"
#include "mov.h"
#include "threadutil.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

namespace {

struct Model {
  std::vector<vec3> slots;                // model slots (with duplicates)
  std::vector<std::vector<int>> faces;    // slot indices
  std::vector<vec3> verts;                // distinct vertices
  std::vector<int> slot_vert;             // slot -> distinct index
  std::vector<std::pair<int, int>> edges;  // distinct vertex pairs
};

Model LoadModel(const std::string &file, double eta) {
  Model m;
  std::ifstream in(file);
  CHECK(in.good()) << file;
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    if (tag == "vertex") {
      int i;
      vec3 p;
      ss >> i >> p.x >> p.y >> p.z;
      m.slots.push_back(p);
    } else if (tag == "face") {
      std::vector<int> f;
      int k;
      while (ss >> k) f.push_back(k);
      m.faces.push_back(f);
    }
  }
  double rmax = 0;
  for (const vec3 &p : m.slots) rmax = std::max(rmax, yocto::length(p));
  for (vec3 &p : m.slots) {
    if (yocto::length(p) > rmax - 1e-9) p = p * (1 + eta);
  }
  for (const vec3 &p : m.slots) {
    int found = -1;
    for (size_t j = 0; j < m.verts.size(); j++) {
      if (yocto::distance(p, m.verts[j]) < 1e-12) found = j;
    }
    if (found < 0) {
      found = m.verts.size();
      m.verts.push_back(p);
    }
    m.slot_vert.push_back(found);
  }
  // Edges: each face's vertices in cyclic order around its centroid (the
  // model lists them by index).
  for (const auto &face : m.faces) {
    std::vector<int> f;
    for (int s : face) {
      const int v = m.slot_vert[s];
      if (std::find(f.begin(), f.end(), v) == f.end()) f.push_back(v);
    }
    vec3 c{0, 0, 0};
    for (int v : f) c += m.verts[v];
    c = c / (double)f.size();
    const vec3 n = yocto::normalize(c), e1 = yocto::normalize(m.verts[f[0]] - c), e2 = yocto::cross(n, e1);
    std::sort(f.begin(), f.end(), [&](int a, int b) {
      return std::atan2(yocto::dot(m.verts[a] - c, e2), yocto::dot(m.verts[a] - c, e1)) <
             std::atan2(yocto::dot(m.verts[b] - c, e2), yocto::dot(m.verts[b] - c, e1));
    });
    for (size_t k = 0; k < f.size(); k++) {
      auto e = std::minmax(f[k], f[(k + 1) % f.size()]);
      if (std::find(m.edges.begin(), m.edges.end(), std::pair<int, int>(e.first, e.second)) == m.edges.end())
        m.edges.push_back({e.first, e.second});
    }
  }
  return m;
}

vec3 Rotate(const vec3 &v, const vec3 &axis, double theta) {
  const vec3 a = yocto::normalize(axis);
  return v * std::cos(theta) + yocto::cross(a, v) * std::sin(theta) +
         a * yocto::dot(a, v) * (1 - std::cos(theta));
}

struct ViewFrame {
  vec3 f, g;
};
ViewFrame NextFrame(const vec3 &u, const std::optional<ViewFrame> &prev) {
  vec3 f = prev.has_value() ? prev->f - u * yocto::dot(prev->f, u) : yocto::cross(vec3{0, 0, 1}, u);
  f = yocto::normalize(f);
  return {f, yocto::cross(u, f)};
}

double Cross2(const vec2 &a, const vec2 &b) { return a.x * b.y - a.y * b.x; }

std::vector<vec2> HullOf(const std::vector<vec2> &pts) {
  std::vector<int> h = Hull2D::QuickHull(pts);
  double area = 0;
  for (size_t i = 0; i < h.size(); i++) area += Cross2(pts[h[i]], pts[h[(i + 1) % h.size()]]);
  if (area < 0) std::reverse(h.begin(), h.end());
  std::vector<vec2> out;
  for (int k : h) out.push_back(pts[k]);
  return out;
}

// Signed distance outside a convex counterclockwise polygon.
double Outside(const std::vector<vec2> &poly, const vec2 &p) {
  double best = -1e300;
  const int n = poly.size();
  for (int i = 0; i < n; i++) {
    const vec2 d = poly[(i + 1) % n] - poly[i];
    const double len = yocto::length(d);
    if (len < 1e-300) continue;
    const vec2 nn{d.y / len, -d.x / len};
    best = std::max(best, yocto::dot(nn, p - poly[i]));
  }
  return best;
}

bool Inside(const std::vector<vec2> &poly, const vec2 &p) {
  const int n = poly.size();
  for (int i = 0; i < n; i++) {
    if (Cross2(poly[(i + 1) % n] - poly[i], p - poly[i]) < 0) return false;
  }
  return true;
}

struct Shadows {
  std::vector<vec2> outer, inner;  // hulls, counterclockwise
  std::vector<vec2> inner_pts;     // every inner vertex
  std::vector<std::pair<vec2, vec2>> outer_edges, inner_edges;  // projected polyhedron edges
  double clearance = 0;            // min depth of an inner vertex (positive: strictly inside)
};

Shadows MakeShadows(const Model &m, const ViewFrame &fr, const vec3 &axis, double theta) {
  const std::vector<vec3> &verts = m.verts;
  std::vector<vec2> o, in;
  for (const vec3 &v : verts) {
    o.push_back({yocto::dot(v, fr.f), yocto::dot(v, fr.g)});
    const vec3 r = Rotate(v, axis, theta);
    in.push_back({yocto::dot(r, fr.f), yocto::dot(r, fr.g)});
  }
  Shadows sh;
  sh.outer = HullOf(o);
  sh.inner = HullOf(in);
  sh.inner_pts = in;
  for (const auto &[a, b] : m.edges) {
    sh.outer_edges.push_back({o[a], o[b]});
    sh.inner_edges.push_back({in[a], in[b]});
  }
  sh.clearance = 1e300;
  for (const vec2 &p : in) sh.clearance = std::min(sh.clearance, -Outside(sh.outer, p));
  return sh;
}

// Outer green, inner red: faint fills and polyhedron edges, bright hulls.
constexpr uint32_t kBackground = 0x0E0E14FF;
constexpr uint32_t kOuter = 0x30E070FF;
constexpr uint32_t kInner = 0xFF3838FF;
constexpr double kFillAlpha = 0.10;
constexpr uint32_t kOuterEdge = 0x30E07058;
constexpr uint32_t kInnerEdge = 0xFF383858;
constexpr uint32_t kOuterLine = 0x40FF80FF;
constexpr uint32_t kInnerLine = 0xFF4848FF;
constexpr uint32_t kFrame = 0x8090B0FF;
constexpr uint32_t kTouch = 0xFFFFFFFF;

uint32_t Mix(uint32_t a, uint32_t b, double t) {
  auto ch = [&](int s) {
    return (uint32_t)std::lround(((a >> s) & 0xFF) * (1 - t) + ((b >> s) & 0xFF) * t) << s;
  };
  return ch(24) | ch(16) | ch(8) | 0xFF;
}

void ClippedLine(ImageRGBA *img, int x0, int y0, int w, int h, vec2 a, vec2 b, float line, uint32_t color) {
  double t0 = 0, t1 = 1;
  const double dx = b.x - a.x, dy = b.y - a.y;
  auto clip = [&](double p, double q) {
    if (p == 0) return q >= 0;
    const double r = q / p;
    if (p < 0) { if (r > t1) return false; t0 = std::max(t0, r); }
    else { if (r < t0) return false; t1 = std::min(t1, r); }
    return true;
  };
  if (clip(-dx, a.x - x0) && clip(dx, x0 + w - 1 - a.x) && clip(-dy, a.y - y0) && clip(dy, y0 + h - 1 - a.y)) {
    img->BlendThickLine32(a.x + t0 * dx, a.y + t0 * dy, a.x + t1 * dx, a.y + t1 * dy, line, color);
  }
}

void PaintWindow(ImageRGBA *img, int x0, int y0, int w, int h, const Shadows &sh, const vec2 &center,
                 double zoom, float line, const std::vector<vec2> &touch) {
  const double cx = x0 + w / 2.0, cy = y0 + h / 2.0;
  auto toPlane = [&](double x, double y) { return center + vec2{(x - cx) / zoom, (cy - y) / zoom}; };
  auto toPix = [&](const vec2 &p) { return vec2{cx + (p.x - center.x) * zoom, cy - (p.y - center.y) * zoom}; };
  ParallelComp(h, [&](int64_t yy) {
    const int y = y0 + yy;
    for (int x = x0; x < x0 + w; x++) {
      int out_n = 0, in_n = 0, pro_n = 0;
      for (int sy = 0; sy < 3; sy++) {
        for (int sx = 0; sx < 3; sx++) {
          const vec2 p = toPlane(x + (sx + 0.5) / 3, y + (sy + 0.5) / 3);
          const bool o = Inside(sh.outer, p), in = Inside(sh.inner, p);
          out_n += o;
          in_n += in && o;
          pro_n += in && !o;
        }
      }
      uint32_t c = Mix(kBackground, kOuter, kFillAlpha * out_n / 9.0);
      // The inner fill; where it leaves the outer shadow (a protrusion) it is stronger.
      c = Mix(c, kInner, kFillAlpha * in_n / 9.0 + 0.5 * pro_n / 9.0);
      img->SetPixel32(x, y, c);
    }
  }, 32);
  // Polyhedron edges (faint; inner on top), then the hulls (bright).
  for (const auto &[a, b] : sh.outer_edges) ClippedLine(img, x0, y0, w, h, toPix(a), toPix(b), line * 0.5f, kOuterEdge);
  for (const auto &[a, b] : sh.inner_edges) ClippedLine(img, x0, y0, w, h, toPix(a), toPix(b), line * 0.5f, kInnerEdge);
  for (size_t i = 0; i < sh.outer.size(); i++) {
    ClippedLine(img, x0, y0, w, h, toPix(sh.outer[i]), toPix(sh.outer[(i + 1) % sh.outer.size()]), line,
                kOuterLine);
  }
  for (size_t i = 0; i < sh.inner.size(); i++) {
    ClippedLine(img, x0, y0, w, h, toPix(sh.inner[i]), toPix(sh.inner[(i + 1) % sh.inner.size()]), line * 0.8f,
                kInnerLine);
  }
  for (const vec2 &t : touch) {
    const vec2 p = toPix(t);
    if (p.x > x0 && p.x < x0 + w && p.y > y0 && p.y < y0 + h) {
      img->BlendThickCircle32(p.x, p.y, std::max(6.0f, line * 4), line * 0.8f, kTouch);
    }
  }
}

// The inner vertices nearest the outer boundary (touching ones first), at
// most k distinct places.
// A reflection symmetry of the picture (both hulls), as a unit axis, if any.
std::optional<vec2> MirrorAxis(const Shadows &sh, double radius) {
  std::vector<vec2> cands;
  for (size_t i = 0; i < sh.outer.size(); i++) {
    cands.push_back(sh.outer[i]);
    cands.push_back((sh.outer[i] + sh.outer[(i + 1) % sh.outer.size()]) * 0.5);
  }
  auto matches = [&](const std::vector<vec2> &pts, const vec2 &ax) {
    for (const vec2 &p : pts) {
      const vec2 r = ax * (2 * yocto::dot(p, ax)) - p;
      bool hit = false;
      for (const vec2 &q : pts) hit = hit || yocto::distance(r, q) < 1e-9 * radius;
      if (!hit) return false;
    }
    return true;
  };
  for (const vec2 &c : cands) {
    if (yocto::length(c) < 1e-9) continue;
    for (const vec2 &ax : {yocto::normalize(c), vec2{-yocto::normalize(c).y, yocto::normalize(c).x}}) {
      if (matches(sh.outer, ax) && matches(sh.inner, ax)) return ax;
    }
  }
  return std::nullopt;
}

std::vector<vec2> ClosePlaces(const Shadows &sh, double radius, int k) {
  const std::optional<vec2> mirror = MirrorAxis(sh, radius);
  std::vector<std::pair<double, vec2>> cand;
  for (const vec2 &p : sh.inner_pts) cand.push_back({std::abs(Outside(sh.outer, p)), p});
  std::sort(cand.begin(), cand.end(), [](const auto &a, const auto &b) { return a.first < b.first; });
  std::vector<vec2> out;
  for (const auto &[d, p] : cand) {
    bool near = false;
    for (const vec2 &q : out) near = near || yocto::distance(p, q) < 0.15 * radius;
    // Skip antipodal duplicates (the picture is centrally symmetric).
    for (const vec2 &q : out) near = near || yocto::distance(p, -q) < 0.15 * radius;
    // And mirror images, when the picture has a reflection symmetry.
    if (mirror.has_value()) {
      for (const vec2 &q : out) {
        const vec2 r = *mirror * (2 * yocto::dot(q, *mirror)) - q;
        near = near || yocto::distance(p, r) < 0.15 * radius || yocto::distance(p, -r) < 0.15 * radius;
      }
    }
    if (!near) out.push_back(p);
    if ((int)out.size() == k) break;
  }
  return out;
}

ImageRGBA Render(int W, int H, const Shadows &sh, double radius, double zoom) {
  ImageRGBA img(W, H);
  img.Clear32(kBackground);
  const int left = H;
  const double sc = 0.42 * H / radius;
  // Touching places: inner vertices within 1e-9 of the outer boundary.
  std::vector<vec2> touch;
  for (const vec2 &p : sh.inner_pts) {
    if (std::abs(Outside(sh.outer, p)) < 1e-9) touch.push_back(p);
  }
  PaintWindow(&img, 0, 0, left, H, sh, vec2{0, 0}, sc, 2.5f, {});
  const std::vector<vec2> places = ClosePlaces(sh, radius, 3);
  const int np = std::max<int>(1, places.size());
  const int pad = H / 40, iw = W - left - 2 * pad, ih = (H - (np + 1) * pad) / np;
  for (size_t i = 0; i < places.size(); i++) {
    const int x0 = left + pad, y0 = pad + i * (ih + pad);
    PaintWindow(&img, x0, y0, iw, ih, sh, places[i], zoom, 3.0f, touch);
    img.BlendThickLine32(x0, y0, x0 + iw, y0, 1.5f, kFrame);
    img.BlendThickLine32(x0, y0 + ih, x0 + iw, y0 + ih, 1.5f, kFrame);
    img.BlendThickLine32(x0, y0, x0, y0 + ih, 1.5f, kFrame);
    img.BlendThickLine32(x0 + iw, y0, x0 + iw, y0 + ih, 1.5f, kFrame);
    const vec2 m{left / 2.0 + places[i].x * sc, H / 2.0 - places[i].y * sc};
    img.BlendThickCircle32(m.x, m.y, H / 60.0, 2.0f, kFrame);
  }
  for (const vec2 &t : touch) {
    img.BlendThickCircle32(left / 2.0 + t.x * sc, H / 2.0 - t.y * sc, H / 200.0, 2.0f, kTouch);
  }
  return img;
}

vec3 ParseVec(const std::string &s) {
  vec3 v{0, 0, 0};
  CHECK(std::sscanf(s.c_str(), "%lf,%lf,%lf", &v.x, &v.y, &v.z) == 3) << s;
  return v;
}

// The pinning plane's normal x = (cos 18, sin 18, 2) / sqrt5 and its tangent
// frame (e1 horizontal, e2 = x cross e1).
struct Wedge {
  vec3 x, e1, e2;
};
Wedge MakeWedge() {
  Wedge w;
  const double d = std::numbers::pi / 10;
  w.x = yocto::normalize(vec3{std::cos(d), std::sin(d), 2});
  w.e1 = yocto::normalize(yocto::cross(w.x, vec3{0, 0, 1}));
  w.e2 = yocto::cross(w.x, w.e1);
  return w;
}

// The tie M(u) = sigma_u sigma_x: rotation by 2 angle(u, x) about x cross u
// normalized (checked by the clearance: 0).
void TieRotation(const vec3 &u, const vec3 &x, vec3 *axis, double *theta) {
  *theta = 2 * std::acos(std::clamp(yocto::dot(u, x), -1.0, 1.0));
  *axis = yocto::normalize(yocto::cross(x, u));
}

void WriteObj(const Model &m, const std::string &file, const vec3 &axis, double theta) {
  FILE *f = fopen(file.c_str(), "w");
  CHECK(f) << file;
  fprintf(f, "# deltoidal hexecontahedron (tieviz); rotated by %.12f rad about (%.12f %.12f %.12f)\n", theta,
          axis.x, axis.y, axis.z);
  for (const vec3 &v : m.verts) {
    const vec3 r = Rotate(v, axis, theta);
    fprintf(f, "v %.12f %.12f %.12f\n", r.x, r.y, r.z);
  }
  for (const auto &face : m.faces) {
    // Orient outward.
    vec3 c{0, 0, 0};
    for (int s : face) c += m.verts[m.slot_vert[s]];
    const vec3 a = m.verts[m.slot_vert[face[0]]], b = m.verts[m.slot_vert[face[1]]],
               d = m.verts[m.slot_vert[face[2]]];
    const bool flip = yocto::dot(yocto::cross(b - a, d - a), c) < 0;
    fprintf(f, "f");
    for (size_t i = 0; i < face.size(); i++) {
      const int s = face[flip ? face.size() - 1 - i : i];
      fprintf(f, " %d", m.slot_vert[s] + 1);
    }
    fprintf(f, "\n");
  }
  fclose(f);
}

}  // namespace

int main(int argc, char **argv) {
  int W = 3840, H = 2160;
  double zoom = 0, eta = 0, theta = 0, seconds = 12, a_off = 0, b_off = 0.15, eps = 0.1;
  std::string model_file = "dh_model.txt", still, tie, wedge, poses, out, mirror, obj;
  std::optional<vec3> view, axis;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--width") W = std::stoi(next());
    else if (a == "--height") H = std::stoi(next());
    else if (a == "--zoom") zoom = std::stod(next());
    else if (a == "--eta") eta = std::stod(next());
    else if (a == "--model") model_file = next();
    else if (a == "--still") still = next();
    else if (a == "--tie") tie = next();
    else if (a == "--wedge") wedge = next();
    else if (a == "--poses") poses = next();
    else if (a == "--out") out = next();
    else if (a == "--mirror") mirror = next();
    else if (a == "--obj") obj = next();
    else if (a == "--view") view = yocto::normalize(ParseVec(next()));
    else if (a == "--axis") axis = yocto::normalize(ParseVec(next()));
    else if (a == "--theta") theta = std::stod(next());
    else if (a == "--seconds") seconds = std::stod(next());
    else if (a == "--a") a_off = std::stod(next());
    else if (a == "--b") b_off = std::stod(next());
    else if (a == "--eps") eps = std::stod(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  if (zoom <= 0) zoom = 40000;
  const Model m = LoadModel(model_file, eta);
  double radius = 0;
  for (const vec3 &v : m.verts) radius = std::max(radius, yocto::length(v));
  const Wedge wd = MakeWedge();

  auto still_image = [&](const vec3 &u, const vec3 &ax, double th, const std::string &file) {
    const ViewFrame fr = NextFrame(u, std::nullopt);
    const Shadows sh = MakeShadows(m, fr, ax, th);
    Render(W, H, sh, radius, zoom).Save(file);
    Print("wrote {}: view ({:.9f} {:.9f} {:.9f}) axis ({:.9f} {:.9f} {:.9f}) theta {:.9f} ({:.3f} deg), "
          "eta {}, clearance {:+.3e}\n", file, u.x, u.y, u.z, ax.x, ax.y, ax.z, th, th * 180 / std::numbers::pi,
          eta, sh.clearance);
    if (!obj.empty()) {
      WriteObj(m, obj + "_outer.obj", vec3{0, 0, 1}, 0);
      WriteObj(m, obj + "_inner.obj", ax, th);
      FILE *f = fopen((obj + "_view.txt").c_str(), "w");
      fprintf(f, "Look along the view direction u (camera at +u looking toward the origin, orthographic):\n"
                 "u = %.12f %.12f %.12f\nin-image right = %.12f %.12f %.12f, up = %.12f %.12f %.12f\n"
                 "inner copy = outer rotated by %.12f rad about %.12f %.12f %.12f (no translation)\n",
              u.x, u.y, u.z, fr.f.x, fr.f.y, fr.f.z, fr.g.x, fr.g.y, fr.g.z, th, ax.x, ax.y, ax.z);
      fclose(f);
      Print("wrote {}_outer.obj, {}_inner.obj, {}_view.txt\n", obj, obj, obj);
    }
  };

  if (!still.empty()) {
    CHECK(view.has_value() && axis.has_value() && theta > 0) << "--still needs --view, --axis, --theta";
    still_image(*view, *axis, theta, still);
  }
  if (!tie.empty()) {
    const vec3 u = yocto::normalize(wd.x + wd.e1 * a_off + wd.e2 * b_off);
    vec3 ax;
    double th;
    TieRotation(u, wd.x, &ax, &th);
    still_image(u, ax, th, tie);
  }
  if (!mirror.empty()) {
    // u0: the 2-fold axis at azimuth 54 degrees, polar atan(2)/2; the mirror
    // tie H_u H_u0 at u = u0 tilted by eps.
    const double az = 0.3 * std::numbers::pi, pol = 0.5 * std::atan(2.0);
    const vec3 u0{std::sin(pol) * std::cos(az), std::sin(pol) * std::sin(az), std::cos(pol)};
    const vec3 t = yocto::normalize(yocto::cross(u0, vec3{0, 0, 1}));
    const vec3 u = yocto::normalize(u0 + yocto::cross(u0, t) * std::tan(eps));
    vec3 ax;
    double th;
    TieRotation(u, u0, &ax, &th);
    still_image(u, ax, th, mirror);
  }
  auto movie = [&](const std::string &file, int n, auto pose_of) {
    auto mov = MOV::OpenOut(file, W, H, MOV::DURATION_60, MOV::Codec::PNG_CCLIB);
    std::optional<ViewFrame> fr;
    for (int i = 0; i < n; i++) {
      vec3 u, ax;
      double th;
      Model mm;
      const Model *mp = pose_of(i, &u, &ax, &th, &mm);
      fr = NextFrame(u, fr);
      const Shadows sh = MakeShadows(*mp, *fr, ax, th);
      mov->AddFrame(Render(W, H, sh, radius, zoom));
      if (i % 60 == 0) Print("frame {}/{}: theta {:.4f} deg, clearance {:+.3e}\n", i, n, th * 180 / std::numbers::pi,
                             sh.clearance);
    }
    MOV::CloseOut(mov);
    Print("wrote {} ({} frames)\n", file, n);
  };
  if (!wedge.empty()) {
    const int n = (int)std::lround(seconds * 60);
    movie(wedge, n, [&](int i, vec3 *u, vec3 *ax, double *th, Model *) -> const Model * {
      // b from 0.002 to 0.2, exponentially at first then steadily.
      const double s = i / (n - 1.0), sm = s * s * (3 - 2 * s);
      const double b = 0.002 * std::pow(100.0, sm);
      *u = yocto::normalize(wd.x + wd.e2 * b);
      TieRotation(*u, wd.x, ax, th);
      return &m;
    });
  }
  if (!poses.empty()) {
    CHECK(!out.empty()) << "--poses needs --out";
    struct Pose { double eta; vec3 u, ax; double th; };
    std::vector<Pose> ps;
    std::ifstream in(poses);
    std::string line;
    while (std::getline(in, line)) {
      Pose p;
      std::istringstream ss(line);
      if (ss >> p.eta >> p.u.x >> p.u.y >> p.u.z >> p.ax.x >> p.ax.y >> p.ax.z >> p.th) ps.push_back(p);
    }
    CHECK(!ps.empty()) << poses;
    movie(out, ps.size(), [&](int i, vec3 *u, vec3 *ax, double *th, Model *mm) -> const Model * {
      *mm = LoadModel(model_file, ps[i].eta);
      *u = yocto::normalize(ps[i].u);
      *ax = yocto::normalize(ps[i].ax);
      *th = ps[i].th;
      return mm;
    });
  }
  return 0;
}
