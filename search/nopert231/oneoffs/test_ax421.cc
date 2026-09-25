#include <iostream>
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

  int k = 14;
  int next_k = 15;
  double psi1 = 0.5 * psi_outer;
  double psi2 = psi_outer;
  double phi1 = k * 2.0 * M_PI / N;
  double phi2 = next_k * 2.0 * M_PI / N;

  vec3 A = yocto::normalize(std::cos(psi1) * u0 + std::sin(psi1) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
  vec3 B = yocto::normalize(std::cos(psi2) * u0 + std::sin(psi2) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
  vec3 C = yocto::normalize(std::cos(psi2) * u0 + std::sin(psi2) * (std::cos(phi2) * ex + std::sin(phi2) * ey));
  vec3 D = yocto::normalize(std::cos(psi1) * u0 + std::sin(psi1) * (std::cos(phi2) * ex + std::sin(phi2) * ey));

  vec3 v421 = vec3{axes[421].center.x.ToDouble() / axes[421].cert.B.ToDouble(),
                   axes[421].center.y.ToDouble() / axes[421].cert.B.ToDouble(),
                   axes[421].center.z.ToDouble() / axes[421].cert.B.ToDouble()};

  std::cout << "Axis 421 on sector 14 quad:\n";
  std::cout << "  dot(A) = " << yocto::dot(A, v421) << "\n";
  std::cout << "  dot(B) = " << yocto::dot(B, v421) << "\n";
  std::cout << "  dot(C) = " << yocto::dot(C, v421) << "\n";
  std::cout << "  dot(D) = " << yocto::dot(D, v421) << "\n";

  // Let's also check other axes on A, B, C, D:
  for (int idx : {421, 1041, 3063, 25, 119, 94}) {
    vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
    std::cout << "Axis " << idx << ":\n";
    std::cout << "  A=" << yocto::dot(A, v) << " B=" << yocto::dot(B, v) << " C=" << yocto::dot(C, v) << " D=" << yocto::dot(D, v) << "\n";
  }

  return 0;
}
