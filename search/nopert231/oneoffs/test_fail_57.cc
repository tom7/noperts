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

  int N = 24;
  std::vector<std::pair<double, double>> rings = {
    {51.0 * M_PI / 180.0, 57.0 * M_PI / 180.0},
    {57.0 * M_PI / 180.0, 73.0 * M_PI / 180.0}
  };

  int r_idx = 0;
  for (auto &ring : rings) {
    double psi1 = ring.first;
    double psi2 = ring.second;
    for (int k = 0; k < N; k++) {
      double phi1 = k * 2.0 * M_PI / N;
      double phi2 = (k + 1) * 2.0 * M_PI / N;

      vec3 p_in1 = std::cos(psi1) * u0_hat + std::sin(psi1) * (std::cos(phi1) * ex + std::sin(phi1) * ey);
      vec3 p_in2 = std::cos(psi1) * u0_hat + std::sin(psi1) * (std::cos(phi2) * ex + std::sin(phi2) * ey);
      vec3 p_out1 = std::cos(psi2) * u0_hat + std::sin(psi2) * (std::cos(phi1) * ex + std::sin(phi1) * ey);
      vec3 p_out2 = std::cos(psi2) * u0_hat + std::sin(psi2) * (std::cos(phi2) * ex + std::sin(phi2) * ey);

      double b1 = -1e9, b2 = -1e9;
      int a1 = -1, a2 = -1;
      for (size_t i = 0; i < v.size(); i++) {
        double d1 = std::min({yocto::dot(p_in1, v[i]), yocto::dot(p_out1, v[i]), yocto::dot(p_out2, v[i])});
        if (d1 > b1) { b1 = d1; a1 = flock_idx[i]; }
        double d2 = std::min({yocto::dot(p_in1, v[i]), yocto::dot(p_out2, v[i]), yocto::dot(p_in2, v[i])});
        if (d2 > b2) { b2 = d2; a2 = flock_idx[i]; }
      }
      if (b1 < 0.001 || b2 < 0.001) {
        std::cout << "Ring " << r_idx << ", sector " << k << " (phi " << phi1*180/M_PI << ".." << phi2*180/M_PI << "): "
                  << "b1=" << b1 << " (ax " << a1 << "), b2=" << b2 << " (ax " << a2 << ")\n";
      }
    }
    r_idx++;
  }

  return 0;
}
