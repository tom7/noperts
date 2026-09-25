#include <iostream>
#include <vector>
#include <cmath>
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
  BigVecQ3 u0_q = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0 = {u0_q.x.ToDouble(), u0_q.y.ToDouble(), u0_q.z.ToDouble()};
  vec3 u0_hat = yocto::normalize(u0);

  vec3 ex = yocto::normalize(yocto::cross(u0_hat, std::abs(u0_hat.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_hat, ex);

  std::vector<vec3> all_v;
  std::vector<int> zero_defect_indices;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      all_v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
      zero_defect_indices.push_back(i);
    }
  }
  std::cout << "Total zero-defect axes: " << all_v.size() << "\n";

  // Test ring [51, 73] deg with all zero-defect axes:
  int N = 24;
  double psi_inner = 51.0 * M_PI / 180.0;
  double psi_outer = 73.0 * M_PI / 180.0;

  int uncertified = 0;
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;

    vec3 p_in1 = std::cos(psi_inner) * u0_hat + std::sin(psi_inner) * (std::cos(phi1) * ex + std::sin(phi1) * ey);
    vec3 p_in2 = std::cos(psi_inner) * u0_hat + std::sin(psi_inner) * (std::cos(phi2) * ex + std::sin(phi2) * ey);
    vec3 p_out1 = std::cos(psi_outer) * u0_hat + std::sin(psi_outer) * (std::cos(phi1) * ex + std::sin(phi1) * ey);
    vec3 p_out2 = std::cos(psi_outer) * u0_hat + std::sin(psi_outer) * (std::cos(phi2) * ex + std::sin(phi2) * ey);

    // Diag 1:
    double b11 = -1e9, b12 = -1e9;
    int a11 = -1, a12 = -1;
    for (size_t i = 0; i < all_v.size(); i++) {
      double d1 = std::min({yocto::dot(p_in1, all_v[i]), yocto::dot(p_out1, all_v[i]), yocto::dot(p_out2, all_v[i])});
      if (d1 > b11) { b11 = d1; a11 = zero_defect_indices[i]; }
      double d2 = std::min({yocto::dot(p_in1, all_v[i]), yocto::dot(p_out2, all_v[i]), yocto::dot(p_in2, all_v[i])});
      if (d2 > b12) { b12 = d2; a12 = zero_defect_indices[i]; }
    }
    bool ok1 = (b11 >= 0.001 && b12 >= 0.001);

    // Diag 2:
    double b21 = -1e9, b22 = -1e9;
    int a21 = -1, a22 = -1;
    for (size_t i = 0; i < all_v.size(); i++) {
      double d1 = std::min({yocto::dot(p_in1, all_v[i]), yocto::dot(p_out1, all_v[i]), yocto::dot(p_in2, all_v[i])});
      if (d1 > b21) { b21 = d1; a21 = zero_defect_indices[i]; }
      double d2 = std::min({yocto::dot(p_in2, all_v[i]), yocto::dot(p_out1, all_v[i]), yocto::dot(p_out2, all_v[i])});
      if (d2 > b22) { b22 = d2; a22 = zero_defect_indices[i]; }
    }
    bool ok2 = (b21 >= 0.001 && b22 >= 0.001);

    if (ok1 || ok2) {
      std::cout << "Sector " << k << " (phi " << phi1*180/M_PI << ".." << phi2*180/M_PI << "): "
                << "CERTIFIED! (axes " << (ok1 ? a11 : a21) << ", " << (ok1 ? a12 : a22) << ")\n";
    } else {
      uncertified++;
      std::cout << "Sector " << k << " (phi " << phi1*180/M_PI << ".." << phi2*180/M_PI << "): "
                << "FAILED: b1=(" << b11 << "," << b12 << "), b2=(" << b21 << "," << b22 << ")\n";
    }
  }

  std::cout << "Total uncertified in ring [51, 73] with all zero-defect axes: " << uncertified << "\n";
  return 0;
}
