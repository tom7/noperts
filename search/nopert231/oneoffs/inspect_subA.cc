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
  double psi_inner = 0.5 * psi_outer;

  double phi1 = 14.0 * 2.0 * M_PI / N;
  vec3 in1 = yocto::normalize(std::cos(psi_inner) * u0 + std::sin(psi_inner) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
  vec3 out1 = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi1) * ex + std::sin(phi1) * ey));

  std::cout << "Checking in1 and out1 individually:\n";
  int cov_in1 = 0, cov_out1 = 0, cov_both = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    bool d1 = (yocto::dot(in1, v) >= 0.0001);
    bool d2 = (yocto::dot(out1, v) >= 0.0001);
    if (d1) cov_in1++;
    if (d2) cov_out1++;
    if (d1 && d2) {
      cov_both++;
      std::cout << "Axis " << i << " covers both in1 and out1! dot(in1)=" << yocto::dot(in1, v)
                << ", dot(out1)=" << yocto::dot(out1, v) << "\n";
    }
  }
  std::cout << "cov_in1 = " << cov_in1 << ", cov_out1 = " << cov_out1 << ", cov_both = " << cov_both << "\n";

  return 0;
}
