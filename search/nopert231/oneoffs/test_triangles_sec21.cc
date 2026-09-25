#include <iostream>
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
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  auto get_v = [&](int idx) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    return yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
  };

  double p1 = 315*M_PI/180.0, p2 = 330*M_PI/180.0;
  double s1 = 51*M_PI/180.0, s2 = 73*M_PI/180.0;
  vec3 p00 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p1)*ex + std::sin(p1)*ey);
  vec3 p01 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p2)*ex + std::sin(p2)*ey);
  vec3 p10 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p1)*ex + std::sin(p1)*ey);
  vec3 p11 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p2)*ex + std::sin(p2)*ey);

  std::cout << "Testing Triangle A1 (p00, p01, p11) and A2 (p00, p10, p11)...\n";
  int best_a1 = -1, best_a2 = -1;
  double max_m1 = -1, max_m2 = -1;

  std::cout << "Testing Triangle B1 (p00, p01, p10) and B2 (p01, p10, p11)...\n";
  int best_b1 = -1, best_b2 = -1;
  double max_mb1 = -1, max_mb2 = -1;

  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = get_v(i);
    double d00 = yocto::dot(p00, v);
    double d01 = yocto::dot(p01, v);
    double d10 = yocto::dot(p10, v);
    double d11 = yocto::dot(p11, v);

    double m_a1 = std::min({d00, d01, d11});
    if (m_a1 > max_m1) { max_m1 = m_a1; best_a1 = i; }

    double m_a2 = std::min({d00, d10, d11});
    if (m_a2 > max_m2) { max_m2 = m_a2; best_a2 = i; }

    double m_b1 = std::min({d00, d01, d10});
    if (m_b1 > max_mb1) { max_mb1 = m_b1; best_b1 = i; }

    double m_b2 = std::min({d01, d10, d11});
    if (m_b2 > max_mb2) { max_mb2 = m_b2; best_b2 = i; }
  }

  std::cout << "Diagonal A:\n";
  std::cout << "  A1 (p00, p01, p11): best axis " << best_a1 << " with min margin " << max_m1 << "\n";
  std::cout << "  A2 (p00, p10, p11): best axis " << best_a2 << " with min margin " << max_m2 << "\n";

  std::cout << "Diagonal B:\n";
  std::cout << "  B1 (p00, p01, p10): best axis " << best_b1 << " with min margin " << max_mb1 << "\n";
  std::cout << "  B2 (p01, p10, p11): best axis " << best_b2 << " with min margin " << max_mb2 << "\n";

  return 0;
}
