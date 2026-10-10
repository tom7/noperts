// turntable: renders a model file's solid spinning, as PNG frames (for an
// animated GIF; see turntable_gif.py). Not used by the proof.
//
// Usage: turntable.exe --model_file septopert_model.txt --out_dir DIR
//                      [--frames 72] [--size 480] [--tilt 0.9] [--elevation 0.35]
//
// The solid's 3-fold axis (1,1,1) is tilted by --tilt radians from the
// screen's vertical, and the solid turns once about that vertical, seen from
// --elevation radians above; the spin shows the apex, the antiprism band and
// the small face in turn. Faces are
// flat shaded and coloured by their orbit under the solid's symmetry
// (classified by how many of their vertices lie in each vertex orbit), with
// dark edges. Orthographic; convex, so back faces are simply culled.
// Rendered at 4x and scaled down for anti-aliasing.

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <format>
#include <fstream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

#include "base/logging.h"
#include "image.h"

namespace {

using Vec = std::array<double, 3>;

Vec Sub(const Vec &a, const Vec &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
Vec Cross(const Vec &a, const Vec &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
double Dot(const Vec &a, const Vec &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
Vec Normalize(const Vec &a) {
  const double n = std::sqrt(Dot(a, a));
  return {a[0] / n, a[1] / n, a[2] / n};
}

// Rotation about a unit axis by an angle (Rodrigues).
Vec Rotate(const Vec &v, const Vec &axis, double angle) {
  const double c = std::cos(angle), s = std::sin(angle);
  const Vec x = Cross(axis, v);
  const double d = Dot(axis, v) * (1.0 - c);
  return {v[0] * c + x[0] * s + axis[0] * d, v[1] * c + x[1] * s + axis[1] * d,
          v[2] * c + x[2] * s + axis[2] * d};
}

struct Model {
  std::vector<Vec> vertices;
  std::vector<std::array<int, 3>> faces;
};

Model ReadModel(const std::string &filename) {
  std::ifstream in(filename);
  CHECK(in.good()) << filename;
  Model model;
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream words(line);
    std::string kind;
    words >> kind;
    if (kind == "vertex") {
      int i;
      Vec v;
      words >> i >> v[0] >> v[1] >> v[2];
      CHECK(i == (int)model.vertices.size()) << line;
      model.vertices.push_back(v);
    } else if (kind == "face") {
      std::array<int, 3> f;
      words >> f[0] >> f[1] >> f[2];
      model.faces.push_back(f);
    }
  }
  CHECK(model.vertices.size() >= 4 && !model.faces.empty()) << filename;
  return model;
}

}  // namespace

int main(int argc, char **argv) {
  std::string model_file = "septopert_model.txt", out_dir;
  int frames = 72, size = 480;
  double tilt = 0.9, elevation = 0.35;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--model_file") model_file = next();
    else if (a == "--out_dir") out_dir = next();
    else if (a == "--frames") frames = std::stoi(next());
    else if (a == "--size") size = std::stoi(next());
    else if (a == "--tilt") tilt = std::stod(next());
    else if (a == "--elevation") elevation = std::stod(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(!out_dir.empty()) << "--out_dir is required";
  const Model model = ReadModel(model_file);
  const int nv = model.vertices.size();

  // Vertex orbits: vertices with the same distance from the origin and the
  // same distance from the 3-fold axis (1,1,1) are symmetric images here.
  const Vec axis3 = Normalize({1, 1, 1});
  std::map<std::pair<long, long>, int> orbit_ids;
  std::vector<int> orbit(nv);
  for (int i = 0; i < nv; i++) {
    const Vec &v = model.vertices[i];
    const auto key = std::make_pair(std::lround(std::sqrt(Dot(v, v)) * 1e6),
                                    std::lround(Dot(v, axis3) * 1e6));
    orbit[i] = orbit_ids.emplace(key, (int)orbit_ids.size()).first->second;
  }
  // Face classes: the multiset of their vertices' orbits.
  std::map<std::vector<int>, int> class_ids;
  std::vector<int> face_class;
  for (const auto &f : model.faces) {
    std::vector<int> key = {orbit[f[0]], orbit[f[1]], orbit[f[2]]};
    std::sort(key.begin(), key.end());
    face_class.push_back(class_ids.emplace(key, (int)class_ids.size()).first->second);
  }
  static constexpr std::array<std::array<double, 3>, 6> kPalette = {{
      {0.93, 0.62, 0.20}, {0.25, 0.55, 0.85}, {0.30, 0.72, 0.45},
      {0.85, 0.35, 0.40}, {0.62, 0.45, 0.80}, {0.85, 0.80, 0.30}}};

  // Outward orientation: the centroid is inside a convex solid.
  Vec centroid = {0, 0, 0};
  for (const Vec &v : model.vertices)
    for (int k = 0; k < 3; k++) centroid[k] += v[k] / nv;

  // Point the 3-fold axis up the screen (y) and tilt it about the screen's
  // x axis; then spin about y and look from slightly above.
  const Vec up = {0, 1, 0};
  const Vec align_axis = Normalize(Cross(axis3, up));
  const double align_angle = std::acos(Dot(axis3, up));
  const Vec xaxis = {1, 0, 0};
  const Vec light = Normalize({-0.4, 0.7, 0.6});

  constexpr int kScale = 4;
  const int big = size * kScale;
  const double radius = 0.42 * big;
  for (int fr = 0; fr < frames; fr++) {
    const double spin = 2.0 * M_PI * fr / frames;
    std::vector<Vec> p(nv);
    for (int i = 0; i < nv; i++) {
      Vec v = Sub(model.vertices[i], centroid);
      v = Rotate(v, align_axis, align_angle);
      v = Rotate(v, xaxis, tilt);
      v = Rotate(v, up, spin);
      p[i] = Rotate(v, xaxis, elevation);
    }
    ImageRGBA img(big, big);
    img.Clear32(0xFFFFFFFF);
    auto sx = [&](const Vec &v) { return (float)(big * 0.5 + v[0] * radius); };
    auto sy = [&](const Vec &v) { return (float)(big * 0.5 - v[1] * radius); };
    for (int fi = 0; fi < (int)model.faces.size(); fi++) {
      const auto &f = model.faces[fi];
      Vec n = Normalize(Cross(Sub(p[f[1]], p[f[0]]), Sub(p[f[2]], p[f[0]])));
      // Orient outward using the original coordinates.
      const Vec &a = model.vertices[f[0]], &b = model.vertices[f[1]], &c = model.vertices[f[2]];
      const Vec n0 = Cross(Sub(b, a), Sub(c, a));
      if (Dot(n0, Sub(a, centroid)) < 0) n = {-n[0], -n[1], -n[2]};
      if (n[2] <= 0) continue;  // Faces away from the viewer at +z.
      const double shade = 0.35 + 0.65 * std::max(0.0, Dot(n, light));
      const auto &col = kPalette[face_class[fi] % kPalette.size()];
      auto channel = [&](double x) { return (uint32_t)std::lround(std::min(1.0, x * shade) * 255); };
      const uint32_t color =
          (channel(col[0]) << 24) | (channel(col[1]) << 16) | (channel(col[2]) << 8) | 0xFF;
      img.BlendTriangle32(sx(p[f[0]]), sy(p[f[0]]), sx(p[f[1]]), sy(p[f[1]]),
                          sx(p[f[2]]), sy(p[f[2]]), color);
      for (int e = 0; e < 3; e++) {
        const Vec &u = p[f[e]], &w = p[f[(e + 1) % 3]];
        img.BlendThickLine32(sx(u), sy(u), sx(w), sy(w), 1.6f * kScale, 0x202020FF);
      }
    }
    const std::string filename = std::format("{}/frame{:03d}.png", out_dir, fr);
    CHECK(img.ScaleDownBy(kScale).Save(filename)) << filename;
  }
  std::printf("%d frames (%d face classes) in %s\n", frames, (int)class_ids.size(), out_dir.c_str());
  return 0;
}
