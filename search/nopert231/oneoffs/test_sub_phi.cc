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

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) all_v.push_back(get_v(i));

  // Test 48 sectors of 7.5 degrees:
  int num_sec = 48;
  double dphi = 360.0 / num_sec;
  double s1 = 51.0 * M_PI / 180.0;
  double s2 = 73.0 * M_PI / 180.0;

  int failed = 0;
  for (int sec = 0; sec < num_sec; sec++) {
    double p1 = (sec * dphi) * M_PI / 180.0;
    double p2 = ((sec + 1) * dphi) * M_PI / 180.0;
    vec3 p00 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p1)*ex + std::sin(p1)*ey);
    vec3 p01 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p2)*ex + std::sin(p2)*ey);
    vec3 p10 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p1)*ex + std::sin(p1)*ey);
    vec3 p11 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p2)*ex + std::sin(p2)*ey);

    // Try both diagonals
    double best_diagA = -1e9, best_diagB = -1e9;
    int a1_ax = -1, a2_ax = -1, b1_ax = -1, b2_ax = -1;

    for (size_t i = 0; i < all_v.size(); i++) {
      vec3 v = all_v[i];
      double d00 = yocto::dot(p00, v), d01 = yocto::dot(p01, v);
      double d10 = yocto::dot(p10, v), d11 = yocto::dot(p11, v);

      double mA1 = std::min({d00, d01, d11});
      if (mA1 > 0.001) a1_ax = i;
      double mA2 = std::min({d00, d10, d11});
      if (mA2 > 0.001) a2_ax = i;

      double mB1 = std::min({d00, d01, d10});
      if (mB1 > 0.001) b1_ax = i;
      double mB2 = std::min({d01, d10, d11});
      if (mB2 > 0.001) b2_ax = i;
    }

    bool okA = (a1_ax >= 0 && a2_ax >= 0);
    bool okB = (b1_ax >= 0 && b2_ax >= 0);

    if (okA || okB) {
      // certified
    } else {
      std::cout << "Sector " << sec << " (phi " << sec*dphi << ".." << (sec+1)*dphi << "): FAILED\n";
      failed++;
    }
  }

  std::cout << "Total failed with 48 sectors: " << failed << "\n";
  return 0;
}
