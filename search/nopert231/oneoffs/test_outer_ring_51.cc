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

  std::vector<int> flock_idx = {3063, 3054, 3034, 22, 24, 119};
  std::vector<vec3> v;
  for (int idx : flock_idx) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  for (int N : {16, 20, 24, 32}) {
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

      double best_val1 = -1e9;
      for (size_t i = 0; i < v.size(); i++) {
        double d = std::min({yocto::dot(p_in1, v[i]), yocto::dot(p_out1, v[i]), yocto::dot(p_out2, v[i])});
        if (d > best_val1) best_val1 = d;
      }
      if (best_val1 < 0.001) uncertified++;

      double best_val2 = -1e9;
      for (size_t i = 0; i < v.size(); i++) {
        double d = std::min({yocto::dot(p_in1, v[i]), yocto::dot(p_out2, v[i]), yocto::dot(p_in2, v[i])});
        if (d > best_val2) best_val2 = d;
      }
      if (best_val2 < 0.001) uncertified++;
    }
    std::cout << "Outer ring N = " << N << " (psi in [51, 73] deg): uncertified = " << uncertified << "\n";
  }

  return 0;
}
