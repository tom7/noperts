// shadowanim: an animation of the first-order rigidity that the proof
// certifies, for video (lossless PNG frames in a .mov, 3840x2160 at 60 Hz by
// default). Not used by the proof. See shadowanim.txt for a description.
//
// For an outer view direction u, the outer shadow is the projection of the
// solid along u. The inner copy is the solid rotated by a small angle theta
// (--theta, default 1e-7 rad: small enough to be first order even at the
// canyon, where a face is nearly edge-on) about an axis w, then translated in the view plane as well as possible
// (an exact LP over the outer hull's edges, as in rigidity-margin's
// PassageClearance). Rupert's property asks for the inner shadow to fit
// strictly inside the outer one. To first order in theta, the inner shadow
// pokes out by theta * m(u) at best, where m(u) is the first-order rigidity
// margin (minimized over w); the proof certifies m > 0 for every view.
//
// The frame shows the outer shadow (filled), the inner shadow's outline,
// and in red the parts of the inner shadow outside the outer one: on the
// left the whole shadow (where the two coincide to the eye), and on the
// right three insets zoomed uniformly (the same zoom for the whole
// animation, --zoom pixels per unit) around the largest protrusions. Phase 1 moves the view from a
// generic view to the canyon (the view of smallest margin, from
// --canyon or found by local search) along a great circle, the angular
// distance to the canyon falling exponentially (from ~60 degrees to 1e-8
// rad), always rotating about the current worst axis: the red shrinks
// almost to nothing. Phase 2
// holds the canyon view and turns the rotation axis once around, from the
// worst axis outward: the red grows away from it.
//
// Usage: shadowanim.exe [--out shadowanim.mov] [--width 3840] [--height 2160]
//          [--seconds1 12] [--seconds2 8] [--zoom 0 (auto)] [--start x,y,z]
//          [--canyon x,y,z] [--frames N (preview: only the first N)]
//          [--snapshots DIR (also every 60th frame as DIR/frame_NNNN.png)]

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <format>
#include <numbers>
#include <optional>
#include <string>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "geom/hull-2d.h"
#include "image.h"
#include "mov.h"
#include "model.h"
#include "rigidity-margin.h"
#include "threadutil.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

namespace {

// The solid's distinct vertices.
std::vector<vec3> Vertices() {
  std::vector<vec3> pts;
  for (int i = 0; i < NUM_VERTICES; i++) {
    const vec3 p = Vertex(i);
    bool dup = false;
    for (const vec3 &q : pts) dup = dup || yocto::distance(p, q) < 1e-12;
    if (!dup) pts.push_back(p);
  }
  return pts;
}

// Dense simplex: maximize c.x s.t. A x <= b, x >= 0, b >= 0 (Bland's rule).
std::optional<std::vector<double>> SimplexMax(const std::vector<std::vector<double>> &A,
                                              const std::vector<double> &b,
                                              const std::vector<double> &c) {
  const int m = A.size(), n = c.size();
  std::vector<std::vector<double>> T(m + 1, std::vector<double>(n + m + 1, 0.0));
  for (int i = 0; i < m; i++) {
    for (int j = 0; j < n; j++) T[i][j] = A[i][j];
    T[i][n + i] = 1.0;
    T[i][n + m] = b[i];
  }
  for (int j = 0; j < n; j++) T[m][j] = -c[j];
  std::vector<int> basis(m);
  for (int i = 0; i < m; i++) basis[i] = n + i;
  for (int iter = 0; iter < 10000; iter++) {
    int col = -1;
    for (int j = 0; j < n + m; j++) {
      if (T[m][j] < -1e-12) { col = j; break; }
    }
    if (col < 0) break;
    int row = -1;
    double best = 0;
    for (int i = 0; i < m; i++) {
      if (T[i][col] > 1e-12) {
        const double r = T[i][n + m] / T[i][col];
        if (row < 0 || r < best - 1e-15 || (std::abs(r - best) <= 1e-15 && basis[i] < basis[row])) {
          row = i;
          best = r;
        }
      }
    }
    if (row < 0) return std::nullopt;
    const double p = T[row][col];
    for (double &x : T[row]) x /= p;
    for (int i = 0; i <= m; i++) {
      if (i == row || T[i][col] == 0.0) continue;
      const double f = T[i][col];
      for (int j = 0; j <= n + m; j++) T[i][j] -= f * T[row][j];
    }
    basis[row] = col;
  }
  std::vector<double> x(n, 0.0);
  for (int i = 0; i < m; i++) if (basis[i] < n) x[basis[i]] = T[i][n + m];
  return x;
}

// The view-plane frame (f, g) for view u, continuous along a path: f is
// the previous frame's f projected onto the plane.
struct ViewFrame {
  vec3 f, g;
};
ViewFrame NextFrame(const vec3 &u, const std::optional<ViewFrame> &prev) {
  vec3 f;
  if (prev.has_value()) {
    f = prev->f - u * yocto::dot(prev->f, u);
  } else {
    const vec3 up{0, 0, 1};
    f = yocto::cross(up, u);
  }
  f = yocto::normalize(f);
  return {f, yocto::cross(u, f)};
}

struct Shadows {
  std::vector<vec2> outer, inner;  // hulls, counterclockwise
  double clearance = 0;            // the LP's best value (negative: protrudes)
};

// Signed distance of p outside a convex counterclockwise polygon (max over
// its edges of the outward offset; positive outside).
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

// The outer shadow, and the inner one (rotated by theta about axis, then
// translated optimally).
Shadows MakeShadows(const std::vector<vec3> &verts, const vec3 &u, const ViewFrame &fr,
                    const vec3 &axis_in, double theta) {
  const vec3 axis = yocto::normalize(axis_in);
  const int nv = verts.size();
  std::vector<vec2> outer(nv), delta(nv);
  const double sn = std::sin(theta), omc = 2.0 * std::sin(0.5 * theta) * std::sin(0.5 * theta);
  for (int k = 0; k < nv; k++) {
    const vec3 &v = verts[k];
    outer[k] = vec2{yocto::dot(v, fr.f), yocto::dot(v, fr.g)};
    const vec3 axv = yocto::cross(axis, v);
    const vec3 d = axv * sn + yocto::cross(axis, axv) * omc;
    delta[k] = vec2{yocto::dot(d, fr.f), yocto::dot(d, fr.g)};
  }
  std::vector<int> hull = Hull2D::QuickHull(outer);
  double area = 0;
  for (size_t i = 0; i < hull.size(); i++) {
    area += rigidity::Cross2(outer[hull[i]], outer[hull[(i + 1) % hull.size()]]);
  }
  if (area < 0) std::reverse(hull.begin(), hull.end());
  // Maximize s subject to n_i . t + s <= g_i (see PassageClearance).
  std::vector<std::vector<double>> A;
  std::vector<double> b;
  std::vector<double> gs;
  const int H = hull.size();
  double big = 0;
  std::vector<vec2> ns;
  for (int i = 0; i < H; i++) {
    const int ia = hull[i], ib = hull[(i + 1) % H];
    const vec2 d = outer[ib] - outer[ia];
    const double len = yocto::length(d);
    if (len < 1e-14) continue;
    const vec2 n{d.y / len, -d.x / len};
    double gi = 1e300;
    for (int k = 0; k < nv; k++) {
      const double base = (k == ia || k == ib) ? 0.0 : yocto::dot(n, outer[ia] - outer[k]);
      gi = std::min(gi, base - yocto::dot(n, delta[k]));
    }
    ns.push_back(n);
    gs.push_back(gi);
    big = std::max(big, std::abs(gi));
  }
  const double scale = big > 0 ? big : 1.0, M = 2.0;
  for (size_t i = 0; i < ns.size(); i++) {
    A.push_back({ns[i].x / scale, -ns[i].x / scale, ns[i].y / scale, -ns[i].y / scale, 1.0});
    b.push_back(gs[i] / scale + M);
  }
  vec2 t{0, 0};
  double s = -1e300;
  if (auto x = SimplexMax(A, b, {0, 0, 0, 0, 1.0})) {
    t = vec2{(*x)[0] - (*x)[1], (*x)[2] - (*x)[3]};
    s = ((*x)[4] - M) * scale;
  }
  Shadows out;
  out.clearance = s;
  for (int k : hull) out.outer.push_back(outer[k]);
  std::vector<vec2> inner(nv);
  for (int k = 0; k < nv; k++) inner[k] = outer[k] + delta[k] + t;
  std::vector<int> ih = Hull2D::QuickHull(inner);
  double ia2 = 0;
  for (size_t i = 0; i < ih.size(); i++) ia2 += rigidity::Cross2(inner[ih[i]], inner[ih[(i + 1) % ih.size()]]);
  if (ia2 < 0) std::reverse(ih.begin(), ih.end());
  for (int k : ih) out.inner.push_back(inner[k]);
  return out;
}

bool Inside(const std::vector<vec2> &poly, const vec2 &p) {
  const int n = poly.size();
  for (int i = 0; i < n; i++) {
    if (rigidity::Cross2(poly[(i + 1) % n] - poly[i], p - poly[i]) < 0) return false;
  }
  return true;
}

constexpr uint32_t kBackground = 0x101018FF;
constexpr uint32_t kOuter = 0x5A6A8AFF;
constexpr uint32_t kInnerLine = 0xF0F0F0FF;
constexpr uint32_t kProtrude = 0xFF3040FF;
constexpr uint32_t kFrame = 0x8090B0FF;

uint32_t Mix(uint32_t a, uint32_t b, double t) {
  auto ch = [&](int s) {
    return (uint32_t)std::lround(((a >> s) & 0xFF) * (1 - t) + ((b >> s) & 0xFF) * t) << s;
  };
  return ch(24) | ch(16) | ch(8) | 0xFF;
}

// Paints the window [x0, x0 + w) x [y0, y0 + h) of img showing the plane
// around `center` at `zoom` pixels per unit: the outer shadow filled, the
// inner one's protrusion in red, and the inner outline.
void PaintWindow(ImageRGBA *img, int x0, int y0, int w, int h, const Shadows &sh,
                 const vec2 &center, double zoom, float line) {
  const double cx = x0 + w / 2.0, cy = y0 + h / 2.0;
  auto toPlane = [&](double x, double y) { return center + vec2{(x - cx) / zoom, (cy - y) / zoom}; };
  auto toPix = [&](const vec2 &p) { return vec2{cx + (p.x - center.x) * zoom, cy - (p.y - center.y) * zoom}; };
  ParallelComp(h, [&](int64_t yy) {
    const int y = y0 + yy;
    for (int x = x0; x < x0 + w; x++) {
      int out_n = 0, pro_n = 0;
      for (int sy = 0; sy < 2; sy++) {
        for (int sx = 0; sx < 2; sx++) {
          const vec2 p = toPlane(x + 0.25 + 0.5 * sx, y + 0.25 + 0.5 * sy);
          const bool o = Inside(sh.outer, p), in = Inside(sh.inner, p);
          out_n += o;
          pro_n += in && !o;
        }
      }
      uint32_t c = Mix(kBackground, kOuter, out_n / 4.0);
      if (pro_n > 0) c = Mix(c, kProtrude, pro_n / 4.0);
      img->SetPixel32(x, y, c);
    }
  }, 32);
  // The inner outline, clipped to the window (segments are long when zoomed).
  for (size_t i = 0; i < sh.inner.size(); i++) {
    vec2 a = toPix(sh.inner[i]), b = toPix(sh.inner[(i + 1) % sh.inner.size()]);
    // Clip the segment to the window (Liang-Barsky).
    double t0 = 0, t1 = 1;
    const double dx = b.x - a.x, dy = b.y - a.y;
    auto clip = [&](double p, double q) {
      if (p == 0) return q >= 0;
      const double r = q / p;
      if (p < 0) { if (r > t1) return false; t0 = std::max(t0, r); }
      else { if (r < t0) return false; t1 = std::min(t1, r); }
      return true;
    };
    if (clip(-dx, a.x - x0) && clip(dx, x0 + w - 1 - a.x) && clip(-dy, a.y - y0) &&
        clip(dy, y0 + h - 1 - a.y)) {
      const vec2 c{a.x + t0 * dx, a.y + t0 * dy}, d{a.x + t1 * dx, a.y + t1 * dy};
      img->BlendThickLine32(c.x, c.y, d.x, d.y, line, kInnerLine);
    }
  }
}

// The three inner vertices protruding most (distinct, and not too close).
std::vector<vec2> Contacts(const Shadows &sh, double radius) {
  std::vector<std::pair<double, vec2>> cand;
  for (const vec2 &p : sh.inner) cand.push_back({Outside(sh.outer, p), p});
  std::sort(cand.begin(), cand.end(), [](const auto &a, const auto &b) { return a.first > b.first; });
  std::vector<vec2> out;
  for (const auto &[d, p] : cand) {
    bool near = false;
    for (const vec2 &q : out) near = near || yocto::distance(p, q) < 0.05 * radius;
    if (!near) out.push_back(p);
    if (out.size() == 3) break;
  }
  return out;
}

// The whole shadow on the left, and three insets on the right zoomed
// uniformly (zoom pixels per unit) around the largest protrusions.
ImageRGBA Render(int W, int H, const Shadows &sh, double radius, double zoom) {
  ImageRGBA img(W, H);
  img.Clear32(kBackground);
  const int left = H;  // a square on the left
  const double sc = 0.42 * H / radius;
  PaintWindow(&img, 0, 0, left, H, sh, vec2{0, 0}, sc, 2.5f);
  const std::vector<vec2> contacts = Contacts(sh, radius);
  const int pad = H / 40, iw = W - left - 2 * pad, ih = (H - 4 * pad) / 3;
  for (size_t i = 0; i < contacts.size(); i++) {
    const int x0 = left + pad, y0 = pad + i * (ih + pad);
    PaintWindow(&img, x0, y0, iw, ih, sh, contacts[i], zoom, 3.0f);
    // Frame the inset, and mark its center on the whole shadow.
    img.BlendThickLine32(x0, y0, x0 + iw, y0, 1.5f, kFrame);
    img.BlendThickLine32(x0, y0 + ih, x0 + iw, y0 + ih, 1.5f, kFrame);
    img.BlendThickLine32(x0, y0, x0, y0 + ih, 1.5f, kFrame);
    img.BlendThickLine32(x0 + iw, y0, x0 + iw, y0 + ih, 1.5f, kFrame);
    const vec2 m{left / 2.0 + contacts[i].x * sc, H / 2.0 - contacts[i].y * sc};
    img.BlendThickCircle32(m.x, m.y, H / 60.0, 2.0f, kFrame);
  }
  return img;
}

vec3 ParseVec(const std::string &s) {
  vec3 v{0, 0, 0};
  CHECK(std::sscanf(s.c_str(), "%lf,%lf,%lf", &v.x, &v.y, &v.z) == 3) << s;
  return yocto::normalize(v);
}

// Spherical interpolation.
vec3 Slerp(const vec3 &a, const vec3 &b, double t) {
  const double om = std::acos(std::clamp(yocto::dot(a, b), -1.0, 1.0));
  if (om < 1e-9) return a;
  return yocto::normalize(a * (std::sin((1 - t) * om) / std::sin(om)) + b * (std::sin(t * om) / std::sin(om)));
}

double Smooth(double t) { return t * t * (3 - 2 * t); }

}  // namespace

int main(int argc, char **argv) {
  std::string out = "shadowanim.mov";
  int W = 3840, H = 2160, max_frames = -1;
  double seconds1 = 12, seconds2 = 8, zoom = 0;
  std::optional<vec3> start, canyon;
  std::string snapshots;
  double theta = 1e-7;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--out") out = next();
    else if (a == "--width") W = std::stoi(next());
    else if (a == "--height") H = std::stoi(next());
    else if (a == "--seconds1") seconds1 = std::stod(next());
    else if (a == "--seconds2") seconds2 = std::stod(next());
    else if (a == "--zoom") zoom = std::stod(next());
    else if (a == "--start") start = ParseVec(next());
    else if (a == "--canyon") canyon = ParseVec(next());
    else if (a == "--frames") max_frames = std::stoi(next());
    else if (a == "--snapshots") snapshots = next();
    else if (a == "--theta") theta = std::stod(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  const std::vector<vec3> verts = Vertices();
  std::vector<rigidity::vec3> rverts(verts.begin(), verts.end());
  double radius = 0;
  for (const vec3 &v : verts) radius = std::max(radius, yocto::length(v));

  // The canyon: the smallest margin over a coarse sphere sample, refined.
  if (!canyon.has_value()) {
    double best = 1e300;
    vec3 bu{0, 0, 1};
    const int N = 20000;
    for (int i = 0; i < N; i++) {
      const double z = 1 - (i + 0.5) / N;  // upper hemisphere (antipodes equivalent)
      const double r = std::sqrt(std::max(0.0, 1 - z * z));
      const double ph = i * std::numbers::pi * (3 - std::sqrt(5.0));
      const vec3 u{r * std::cos(ph), r * std::sin(ph), z};
      const double m = rigidity::FirstOrderMargin(rverts, u, false).m;
      if (m < best) { best = m; bu = u; }
    }
    auto [m, u] = rigidity::RefineView(rverts, bu);
    canyon = yocto::normalize(u);
    Print("canyon: ({:.9f}, {:.9f}, {:.9f}), margin {:.4e}\n", canyon->x, canyon->y, canyon->z, m);
  }
  if (!start.has_value()) {
    // A generic view about 60 degrees from the canyon.
    const vec3 side = yocto::normalize(yocto::cross(*canyon, vec3{0.3, 0.5, 0.8}));
    start = yocto::normalize(*canyon * 0.5 + side * std::sqrt(0.75));
  }
  // The insets' zoom (fixed for the whole animation): the largest
  // protrusion at the start view spans about 30% of an inset's height.
  if (zoom <= 0) {
    const auto m0 = rigidity::FirstOrderMargin(rverts, *start, false);
    const double prot = std::max(1e-15, theta * std::abs(m0.m));
    zoom = 0.3 * ((H - 4 * (H / 40)) / 3.0) / prot;
  }
  Print("theta {} rad, inset zoom {:.3e} pixels per unit\n", theta, zoom);

  auto mov = MOV::OpenOut(out, W, H, MOV::DURATION_60, MOV::Codec::PNG_CCLIB);
  const int n1 = (int)std::lround(seconds1 * 60), n2 = (int)std::lround(seconds2 * 60);
  std::optional<ViewFrame> fr;
  int frames = 0;
  std::string log;
  for (int i = 0; i < n1 + n2 && (max_frames < 0 || frames < max_frames); i++) {
    vec3 u, axis;
    if (i < n1) {
      // The angular distance to the canyon falls exponentially (the canyon
      // is narrow: the margin drops only very close to it).
      const double d0 = std::acos(std::clamp(yocto::dot(*start, *canyon), -1.0, 1.0));
      const double s01 = Smooth(i / (n1 - 1.0));
      const double d = i == n1 - 1 ? 0.0 : d0 * std::pow(10.0, -s01 * std::log10(d0 / 1e-8));
      u = Slerp(*canyon, *start, d / d0);
      axis = rigidity::FirstOrderMargin(rverts, u, false).axis;
    } else {
      // Turn the axis away from the worst one and back, around the view.
      u = *canyon;
      const vec3 w0 = rigidity::FirstOrderMargin(rverts, u, false).axis;
      const vec3 e = yocto::normalize(yocto::cross(w0, std::abs(w0.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0}));
      const double ang = 0.5 * std::numbers::pi * std::sin(std::numbers::pi * (i - n1) / (n2 - 1.0));
      axis = w0 * std::cos(ang) + e * std::sin(ang);
    }
    fr = NextFrame(u, fr);
    const Shadows sh = MakeShadows(verts, u, *fr, axis, theta);
    const ImageRGBA img = Render(W, H, sh, radius, zoom);
    mov->AddFrame(img);
    if (!snapshots.empty() && (i % 60 == 0 || i == n1 - 1)) img.Save(std::format("{}/frame_{:04d}.png", snapshots, i));
    log += std::format("{} {:+.9f} {:+.9f} {:+.9f} {:+.6e}\n", i, u.x, u.y, u.z, sh.clearance / theta);
    if (i % 60 == 0 || i == n1 - 1) {
      const auto mm = rigidity::FirstOrderMargin(rverts, u, false);
      Print("frame {}: clearance/theta {:+.4e}, first-order margin {:.4e}, cube margin {:.4e}\n", i,
            sh.clearance / theta, mm.m_euclid_upper, mm.m);
    }
    frames++;
    if (frames % 60 == 0) Print("  {} frames\n", frames);
  }
  MOV::CloseOut(mov);
  Print("wrote {} ({} frames)\n", out, frames);
  return 0;
}
