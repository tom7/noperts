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

  auto get_v = [&](int idx) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    return yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
  };

  std::vector<int> flock_idx = {3063, 3054, 3034, 22, 24, 119};

  int N = 24;
  int k = 21;
  double phi1 = k * 2.0 * M_PI / N;
  double phi2 = (k + 1) * 2.0 * M_PI / N;
  double psi1 = 51.0 * M_PI / 180.0;
  double psi2 = 55.0 * M_PI / 180.0;

  auto pt = [&](double psi, double phi) {
    return std::cos(psi) * u0_hat + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey);
  };

  vec3 p_in1 = pt(psi1, phi1);
  vec3 p_in2 = pt(psi1, phi2);
  vec3 p_out1 = pt(psi2, phi1);
  vec3 p_out2 = pt(psi2, phi2);

  std::cout << "phi1 = " << phi1*180/M_PI << ", phi2 = " << phi2*180/M_PI << "\n";
  std::cout << "psi1 = " << psi1*180/M_PI << ", psi2 = " << psi2*180/M_PI << "\n";

  for (int idx : flock_idx) {
    vec3 v = get_v(idx);
    std::cout << "Axis " << idx << ":\n";
    std::cout << "  in1:  " << yocto::dot(p_in1, v) << "\n";
    std::cout << "  in2:  " << yocto::dot(p_in2, v) << "\n";
    std::cout << "  out1: " << yocto::dot(p_out1, v) << "\n";
    std::cout << "  out2: " << yocto::dot(p_out2, v) << "\n";
  }

  return 0;
}
