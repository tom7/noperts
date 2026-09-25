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
  int R_rings = 2;
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

  std::cout << "outerA_14 vertices:\n";
  std::cout << "A (inner): " << A.x << ", " << A.y << ", " << A.z << "\n";
  std::cout << "B (outer1): " << B.x << ", " << B.y << ", " << B.z << "\n";
  std::cout << "C (outer2): " << C.x << ", " << C.y << ", " << C.z << "\n";

  // Check which axes come closest to covering A, B, C:
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double dA = yocto::dot(A, v);
    double dB = yocto::dot(B, v);
    double dC = yocto::dot(C, v);
    double min_d = std::min({dA, dB, dC});
    if (min_d > -0.005) {
      std::cout << "Axis " << i << ": dA=" << dA << ", dB=" << dB << ", dC=" << dC << " (min=" << min_d << ")\n";
    }
  }

  // If we split outerA_14: midpoint of BC:
  vec3 M_BC = yocto::normalize(0.5 * (B + C));
  std::cout << "\nTesting with midpoint of BC:\n";
  double best_T1 = -1e9, best_T2 = -1e9;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d1 = std::min({yocto::dot(A, v), yocto::dot(B, v), yocto::dot(M_BC, v)});
    if (d1 > best_T1) best_T1 = d1;
    double d2 = std::min({yocto::dot(A, v), yocto::dot(M_BC, v), yocto::dot(C, v)});
    if (d2 > best_T2) best_T2 = d2;
  }
  std::cout << "T1 (A, B, M): best min_d = " << best_T1 << "\n";
  std::cout << "T2 (A, M, C): best min_d = " << best_T2 << "\n";

  return 0;
}
