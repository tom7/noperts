#include <iomanip>
#include <iostream>
#include <vector>
#include <cmath>
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

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double phi14 = 14.0 * 2.0 * M_PI / 16.0;
  vec3 dir14 = std::cos(phi14) * ex + std::sin(phi14) * ey;

  std::vector<int> test_axes = {3063, 3066, 3054, 1041, 119, 94, 25};

  std::cout << "psi_deg | " ;
  for (int idx : test_axes) std::cout << "ax" << idx << "    | ";
  std::cout << "max\n";

  for (double psi_deg = 30.0; psi_deg <= 75.0; psi_deg += 2.5) {
    double psi = psi_deg * M_PI / 180.0;
    vec3 p = yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * dir14);
    double max_dot = -1e9;
    std::cout << std::fixed << std::setprecision(1) << psi_deg << "    | ";
    for (int idx : test_axes) {
      vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                    axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                    axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
      double d = yocto::dot(p, v);
      if (d > max_dot) max_dot = d;
      std::cout << std::fixed << std::setprecision(5) << d << " | ";
    }
    std::cout << std::fixed << std::setprecision(5) << max_dot << "\n";
  }

  return 0;
}
