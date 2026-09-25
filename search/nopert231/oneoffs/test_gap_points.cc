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
  double norm_u0 = std::sqrt(u0_sq.ToDouble());
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  // What is the max c_cone supported by the complement cage (22, 11, 7)?
  // Let's check c_cone = 0.018, 0.017, 0.016, 0.015
  std::vector<vec3> lam_pos_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      BigVecQ3 uc = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
      BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
      if (dot > 0) {
        lam_pos_axes.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
      }
    }
  }

  vec3 z = u0_f;
  vec3 x = yocto::normalize(yocto::cross(z, std::abs(z.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 y = yocto::cross(z, x);

  for (double c_cone : {0.020, 0.022, 0.024, 0.026, 0.027, 0.028, 0.030}) {
    double cos_alpha = c_cone / norm_u0;
    if (cos_alpha >= 1.0) continue;
    int covered = 0;
    int N = 2000;
    for (int i = 0; i < N; i++) {
      double t = (double)i / (N - 1.0);
      double cos_theta = 1.0 - t * (1.0 - cos_alpha);
      double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
      double phi = i * 2.399963229728653;
      vec3 p = (std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z;
      vec3 p_norm = yocto::normalize(p);
      bool ok = false;
      for (const auto &v : lam_pos_axes) {
        if (yocto::dot(p_norm, v) >= 0.005) {
          ok = true; break;
        }
      }
      if (ok) covered++;
    }
    double angle_deg = std::acos(cos_alpha) * 180.0 / M_PI;
    std::cout << "c_cone = " << c_cone << " (alpha = " << angle_deg << " deg): "
              << covered << " / " << N << " (" << (100.0 * covered / N) << "%)\n";
  }
  return 0;
}
