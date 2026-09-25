#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);
  double norm_u0 = yocto::length(u0_raw);

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  int N = 16;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  double psi1 = 0.5 * psi_outer;
  double psi2 = psi_outer;

  // Let's sweep phi between sector 14 (14.0/16) and sector 15 (15.0/16):
  std::cout << "phi_frac | best_v_psi1 | dot1 | best_v_psi2 | dot2\n";
  for (double f = 14.0; f <= 15.01; f += 0.1) {
    double phi = f * 2.0 * M_PI / N;
    vec3 p1 = yocto::normalize(std::cos(psi1) * u0 + std::sin(psi1) * (std::cos(phi) * ex + std::sin(phi) * ey));
    vec3 p2 = yocto::normalize(std::cos(psi2) * u0 + std::sin(psi2) * (std::cos(phi) * ex + std::sin(phi) * ey));

    double max1 = -1e9, max2 = -1e9;
    int best1 = -1, best2 = -1;
    for (size_t i = 0; i < axes.size(); i++) {
      vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
      double d1 = yocto::dot(p1, v);
      if (d1 > max1) { max1 = d1; best1 = i; }
      double d2 = yocto::dot(p2, v);
      if (d2 > max2) { max2 = d2; best2 = i; }
    }
    std::cout << f << " | ax" << best1 << " | " << max1 << " | ax" << best2 << " | " << max2 << "\n";
  }

  return 0;
}
