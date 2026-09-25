#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Loaded " << base_axes.size() << " hull support axes.\n";

  struct Cand {
    int idx;
    vec3 u;
  };
  std::vector<Cand> cands;
  for (size_t i = 0; i < base_axes.size(); i++) {
    const auto &ax = base_axes[i];
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    cands.push_back({(int)i, u});
  }

  double delta = 0.000234013;
  double c_cone = 0.040;
  double box_c = 0.001;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::vector<Cand> filtered;
  std::vector<vec3> dirs = {
    {1, 0, 0}, {-1, 0, 0}, {0, 1, 0}, {0, -1, 0}, {0, 0, 1}, {0, 0, -1},
    {1, 1, 0}, {-1, 1, 0}, {1, -1, 0}, {-1, -1, 0},
    {1, 0, 1}, {-1, 0, 1}, {1, 0, -1}, {-1, 0, -1},
    {0, 1, 1}, {0, -1, 1}, {0, 1, -1}, {0, -1, -1}
  };
  for (const auto &d : dirs) {
    std::sort(cands.begin(), cands.end(), [&](const Cand &a, const Cand &b) {
      return yocto::dot(a.u, d) > yocto::dot(b.u, d);
    });
    for (int i = 0; i < std::min((int)cands.size(), 20); i++) {
      bool exists = false;
      for (const auto &f : filtered) {
        if (f.idx == cands[i].idx) { exists = true; break; }
      }
      if (!exists) filtered.push_back(cands[i]);
    }
  }
  std::cout << "Filtered to " << filtered.size() << " promising directional axes.\n";

  int N = filtered.size();
  double best_min_l = -1.0;
  int bi = -1, bj = -1, bk = -1;

  for (int i = 0; i < N; i++) {
    vec3 v1 = filtered[i].u;
    for (int j = i + 1; j < N; j++) {
      vec3 v2 = filtered[j].u;
      for (int k = j + 1; k < N; k++) {
        vec3 v3 = filtered[k].u;

        vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
        double det = yocto::dot(d1, yocto::cross(d2, d3));
        if (std::abs(det) < 1e-8) continue;
        vec3 c23 = yocto::cross(d2, d3);

        double min_l = 1e9;
        for (const auto &p : oct) {
          vec3 dp = p - v0;
          double l1 = yocto::dot(dp, c23) / det;
          double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
          double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
          double l0 = 1.0 - l1 - l2 - l3;
          min_l = std::min({min_l, l0, l1, l2, l3});
          if (min_l <= 0) break;
        }

        if (min_l > best_min_l) {
          best_min_l = min_l;
          bi = i; bj = j; bk = k;
          std::cout << "Found enclosing cage: min_l = " << min_l
                    << " with filtered indices (" << bi << ", " << bj << ", " << bk << ")\n";
        }
      }
    }
  }

  if (best_min_l > 0) {
    std::cout << "SUCCESS! Found cage enclosing octahedron with c_cone = " << c_cone << "!\n";
    std::cout << "Axes:\n";
    for (int idx : {bi, bj, bk}) {
      const auto &c = filtered[idx];
      const auto &ax = base_axes[c.idx];
      std::cout << "Axis " << c.idx << ": u = (" << c.u.x << ", " << c.u.y << ", " << c.u.z
                << "), B = " << ax.cert.B.ToString() << "\n";
      std::cout << "  center = (" << ax.center.x.ToString() << ", "
                << ax.center.y.ToString() << ", " << ax.center.z.ToString() << ")\n";
    }
  } else {
    std::cout << "No enclosing cage found in this filtered subset. Best min_l = " << best_min_l << "\n";
  }

  return 0;
}
