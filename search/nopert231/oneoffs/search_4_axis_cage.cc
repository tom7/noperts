#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static double Det3(vec3 a, vec3 b, vec3 c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  std::cout << "Hull support axes: " << axes.size() << "\n";

  struct ZeroDefAxis {
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    vec3 u;
    int orig_idx;
  };
  std::vector<ZeroDefAxis> zd_axes;
  std::string err;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 u = {ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
      zd_axes.push_back({cert, ctr, del, u, (int)i});
    }
  }
  std::cout << "Strictly zero-defect axes from hull: " << zd_axes.size() << "\n";

  ContactInfo new_c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {8, 9, 9, 10, 0, 9}
  };
  AxisCertificate c0_cert; BigVecQ3 c0_ctr; BigRat c0_del;
  if (Tube229::AuditAxis(tri, new_c0, &c0_cert, &c0_ctr, &c0_del, &err, BigRat(0))) {
    vec3 u = {c0_ctr.x.ToDouble() / c0_cert.B.ToDouble(),
              c0_ctr.y.ToDouble() / c0_cert.B.ToDouble(),
              c0_ctr.z.ToDouble() / c0_cert.B.ToDouble()};
    zd_axes.push_back({c0_cert, c0_ctr, c0_del, u, -1});
    std::cout << "Added new u0 to zd_axes (total: " << zd_axes.size() << ")\n";
  }

  double best_c = 0;
  int best_quad[4] = {-1, -1, -1, -1};
  int u0_idx = zd_axes.size() - 1;
  vec3 p0 = zd_axes[u0_idx].u;

  for (size_t i = 0; i < zd_axes.size() - 1; i++) {
    vec3 p1 = zd_axes[i].u;
    for (size_t j = i + 1; j < zd_axes.size() - 1; j++) {
      vec3 p2 = zd_axes[j].u;
      for (size_t k = j + 1; k < zd_axes.size() - 1; k++) {
        vec3 p3 = zd_axes[k].u;

        vec3 a = p0 - p3, b = p1 - p3, d = p2 - p3;
        double det = Det3(a, b, d);
        if (std::abs(det) < 1e-12) continue;
        vec3 y0 = -p3;
        double l0 = Det3(y0, b, d) / det;
        double l1 = Det3(a, y0, d) / det;
        double l2 = Det3(a, b, y0) / det;
        double l3 = 1.0 - l0 - l1 - l2;
        if (l0 <= 1e-5 || l1 <= 1e-5 || l2 <= 1e-5 || l3 <= 1e-5) continue;

        auto dist_face = [](vec3 v0, vec3 v1, vec3 v2) {
          vec3 n = yocto::cross(v1 - v0, v2 - v0);
          double len = yocto::length(n);
          if (len < 1e-12) return 0.0;
          return std::abs(yocto::dot(v0, n)) / len;
        };
        double d0 = dist_face(p1, p2, p3);
        double d1 = dist_face(p0, p2, p3);
        double d2 = dist_face(p0, p1, p3);
        double d3 = dist_face(p0, p1, p2);
        double min_d = std::min({d0, d1, d2, d3});
        if (min_d > best_c) {
          best_c = min_d;
          best_quad[0] = u0_idx; best_quad[1] = i; best_quad[2] = j; best_quad[3] = k;
          std::cout << "New best 4-axis cage inradius c = " << best_c << " with ("
                    << i << ", " << j << ", " << k << ")\n";
        }
      }
    }
  }

  std::cout << "Overall best 4-axis cage inradius c = " << best_c << "\n";
  return 0;
}
