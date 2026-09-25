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

  vec3 v3063 = get_v(3063);
  vec3 v22 = get_v(22);
  vec3 v24 = get_v(24);

  double p1 = 315*M_PI/180.0, p2 = 330*M_PI/180.0;
  double s1 = 51*M_PI/180.0, s_mid = 54.5*M_PI/180.0, s2 = 73*M_PI/180.0;
  vec3 p00 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p1)*ex + std::sin(p1)*ey);
  vec3 p01 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p2)*ex + std::sin(p2)*ey);
  vec3 p_mid = std::cos(s_mid)*u0 + std::sin(s_mid)*(std::cos(p1)*ex + std::sin(p1)*ey);
  vec3 p10 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p1)*ex + std::sin(p1)*ey);
  vec3 p11 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p2)*ex + std::sin(p2)*ey);

  std::cout << "Triangle 1 (p00, p01, p_mid) with 3063:\n";
  std::cout << "  p00: " << yocto::dot(p00, v3063) << "\n";
  std::cout << "  p01: " << yocto::dot(p01, v3063) << "\n";
  std::cout << "  p_mid: " << yocto::dot(p_mid, v3063) << "\n";

  std::cout << "Triangle 2 (p_mid, p10, p11) with 22:\n";
  std::cout << "  p_mid: " << yocto::dot(p_mid, v22) << "\n";
  std::cout << "  p10: " << yocto::dot(p10, v22) << "\n";
  std::cout << "  p11: " << yocto::dot(p11, v22) << "\n";

  std::cout << "Triangle 3 (p_mid, p01, p11) with 24:\n";
  std::cout << "  p_mid: " << yocto::dot(p_mid, v24) << "\n";
  std::cout << "  p01: " << yocto::dot(p01, v24) << "\n";
  std::cout << "  p11: " << yocto::dot(p11, v24) << "\n";

  // Also check all other axes on Triangle 3:
  int best_t3 = -1; double max_m3 = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = get_v(i);
    double m = std::min({yocto::dot(p_mid, v), yocto::dot(p01, v), yocto::dot(p11, v)});
    if (m > max_m3) { max_m3 = m; best_t3 = i; }
  }
  std::cout << "Triangle 3 best axis: " << best_t3 << " with margin " << max_m3 << "\n";

  return 0;
}
