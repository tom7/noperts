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
  double c_core = 0.0005;

  int N = 16;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  double psi1 = 0.5 * psi_outer;
  double psi2 = psi_outer;

  auto get_pt = [&](double psi, double f) {
    double phi = f * 2.0 * M_PI / N;
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
    for (size_t i = 0; i < axes.size(); i++) {
      vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
      if (yocto::dot(p1, v) >= c_core && yocto::dot(p2, v) >= c_core && yocto::dot(p3, v) >= c_core) {
        return (int)i;
      }
    }
    return -1;
  };

  // Subquad 1: 14 to 14.5
  vec3 A1 = get_pt(psi1, 14.0);
  vec3 B1 = get_pt(psi2, 14.0);
  vec3 C1 = get_pt(psi2, 14.5);
  vec3 D1 = get_pt(psi1, 14.5);

  std::cout << "Subquad 14.0 - 14.5:\n";
  std::cout << "  diag 1: T1(A,B,C)=" << check_tri(A1, B1, C1) << " T2(A,C,D)=" << check_tri(A1, C1, D1) << "\n";
  std::cout << "  diag 2: T3(B,C,D)=" << check_tri(B1, C1, D1) << " T4(B,D,A)=" << check_tri(B1, D1, A1) << "\n";

  // Subquad 2: 14.5 to 15.0
  vec3 A2 = get_pt(psi1, 14.5);
  vec3 B2 = get_pt(psi2, 14.5);
  vec3 C2 = get_pt(psi2, 15.0);
  vec3 D2 = get_pt(psi1, 15.0);

  std::cout << "Subquad 14.5 - 15.0:\n";
  std::cout << "  diag 1: T1(A,B,C)=" << check_tri(A2, B2, C2) << " T2(A,C,D)=" << check_tri(A2, C2, D2) << "\n";
  std::cout << "  diag 2: T3(B,C,D)=" << check_tri(B2, C2, D2) << " T4(B,D,A)=" << check_tri(B2, D2, A2) << "\n";

  return 0;
}
