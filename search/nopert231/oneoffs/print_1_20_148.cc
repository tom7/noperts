#include <iostream>
#include <vector>
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

  int idx1 = filtered[1].idx;
  int idx2 = filtered[20].idx;
  int idx3 = filtered[148].idx;

  std::cout << "Original indices: " << idx1 << ", " << idx2 << ", " << idx3 << "\n";
  std::cout << "u1: " << filtered[1].u.x << ", " << filtered[1].u.y << ", " << filtered[1].u.z << "\n";
  std::cout << "u2: " << filtered[20].u.x << ", " << filtered[20].u.y << ", " << filtered[20].u.z << "\n";
  std::cout << "u3: " << filtered[148].u.x << ", " << filtered[148].u.y << ", " << filtered[148].u.z << "\n";

  double delta = 0.000234013;
  double box_c = 0.001;
  double c_cone = 0.040;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 v1 = filtered[1].u;
  vec3 v2 = filtered[20].u;
  vec3 v3 = filtered[148].u;

  vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
  double det = yocto::dot(d1, yocto::cross(d2, d3));
  vec3 c23 = yocto::cross(d2, d3);

  for (int p_idx = 0; p_idx < 6; p_idx++) {
    vec3 dp = oct[p_idx] - v0;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
    double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    std::cout << "Oct vertex " << p_idx << ": l0=" << l0 << ", l1=" << l1
              << ", l2=" << l2 << ", l3=" << l3
              << " (min = " << std::min({l0, l1, l2, l3}) << ")\n";
  }

  return 0;
}
