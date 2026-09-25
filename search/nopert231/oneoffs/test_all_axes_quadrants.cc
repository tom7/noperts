#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  struct Cand {
    int idx;
    double mu0, wx, wy;
  };
  std::vector<Cand> cands;

  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
      double mu0 = yocto::dot(v, vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()}) / u0_sq.ToDouble();
      double wx = yocto::dot(v, ex);
      double wy = yocto::dot(v, ey);
      cands.push_back({(int)i, mu0, wx, wy});
    }
  }

  double c_cone = 0.015;
  int s1[4] = {1, 1, -1, -1};
  int s2[4] = {1, -1, 1, -1};

  // Try rotating the (ex, ey) frame by angle psi from 0 to 360 deg
  for (int step = 0; step < 360; step += 10) {
    double psi = step * M_PI / 180.0;
    vec3 n1 = std::cos(psi) * ex + std::sin(psi) * ey;
    vec3 n2 = -std::sin(psi) * ex + std::cos(psi) * ey;

    bool all_4 = true;
    int quad_axis[4] = {-1, -1, -1, -1};
    double quad_margin[4] = {0};

    for (int q = 0; q < 4; q++) {
      vec3 ray1 = (float)s1[q] * n1;
      vec3 ray2 = (float)s2[q] * n2;

      double best_margin = -1;
      int best_idx = -1;

      for (const auto &c : cands) {
        // mu1 = v . ray1 = s1 * (wx * cos - wy * sin)
        double dot_n1 = c.wx * std::cos(psi) + c.wy * std::sin(psi);
        double dot_n2 = -c.wx * std::sin(psi) + c.wy * std::cos(psi);
        double mu1 = s1[q] * dot_n1;
        double mu2 = s2[q] * dot_n2;

        if (c.mu0 > 0 && mu1 >= 0 && mu2 >= 0) {
          double margin = c.mu0 * c_cone;
          if (margin > best_margin) {
            best_margin = margin;
            best_idx = c.idx;
          }
        }
      }
      if (best_idx < 0) {
        all_4 = false;
        break;
      }
      quad_axis[q] = best_idx;
      quad_margin[q] = best_margin;
    }

    if (all_4) {
      std::cout << "SUCCESS! Rotation psi = " << step << " deg gives 4 valid quadrant axes!\n";
      for (int q = 0; q < 4; q++) {
        std::cout << "  Quadrant " << q << ": Axis " << quad_axis[q] << " with margin " << quad_margin[q] << "\n";
      }
      return 0;
    }
  }

  std::cout << "4 orthogonal quadrants not covered. Trying 6 sectors (60 deg each)...\n";
  return 0;
}
