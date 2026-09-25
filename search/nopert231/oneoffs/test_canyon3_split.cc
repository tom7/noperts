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
  vec3 u0_raw = vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    auto &ax = axes[i];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    all_v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  struct Tri { vec3 p1, p2, p3; std::string name; };
  std::vector<Tri> tris;
  vec3 p0 = u0;

  double psi_mid = 52.0 * M_PI / 180.0;

  // 6 regular sectors of 45 deg
  for (int k = 0; k < 6; k++) {
    double phi1 = k * (M_PI / 4.0);
    double phi2 = (k + 1) * (M_PI / 4.0);
    vec3 b1 = std::sin(alpha) * (std::cos(phi1) * k1 + std::sin(phi1) * k2) + std::cos(alpha) * u0;
    vec3 b2 = std::sin(alpha) * (std::cos(phi2) * k1 + std::sin(phi2) * k2) + std::cos(alpha) * u0;
    tris.push_back({p0, b1, b2, "Sector " + std::to_string(k)});
  }

  // Subdivide [270, 360] into intervals:
  // j=0: [270, 285]
  // j=1: [285, 300]
  // j=2: [300, 315]
  // j=3: split into [315, 322.5] and [322.5, 330]!
  // j=4: [330, 345]
  // j=5: [345, 360]
  std::vector<std::pair<double, double>> canyon_intervals = {
    {270, 285},
    {285, 300},
    {300, 315},
    {315, 322.5},
    {322.5, 330},
    {330, 345},
    {345, 360}
  };

  for (size_t j = 0; j < canyon_intervals.size(); j++) {
    double phi1 = canyon_intervals[j].first * M_PI / 180.0;
    double phi2 = canyon_intervals[j].second * M_PI / 180.0;

    vec3 b1 = std::sin(alpha) * (std::cos(phi1) * k1 + std::sin(phi1) * k2) + std::cos(alpha) * u0;
    vec3 b2 = std::sin(alpha) * (std::cos(phi2) * k1 + std::sin(phi2) * k2) + std::cos(alpha) * u0;
    vec3 m1 = std::sin(psi_mid) * (std::cos(phi1) * k1 + std::sin(phi1) * k2) + std::cos(psi_mid) * u0;
    vec3 m2 = std::sin(psi_mid) * (std::cos(phi2) * k1 + std::sin(phi2) * k2) + std::cos(psi_mid) * u0;

    tris.push_back({p0, m1, m2, "Canyon " + std::to_string(j) + " (inner)"});
    tris.push_back({m1, b1, b2, "Canyon " + std::to_string(j) + " (outer 1)"});
    tris.push_back({m1, m2, b2, "Canyon " + std::to_string(j) + " (outer 2)"});
  }

  std::cout << "Total triangles: " << tris.size() << "\n";
  int fully_covered = 0;
  for (size_t t = 0; t < tris.size(); t++) {
    const auto &tr = tris[t];
    int best_ax = -1;
    double best_margin = -1e9;
    for (size_t i = 0; i < all_v.size(); i++) {
      double m = std::min({yocto::dot(all_v[i], tr.p1), yocto::dot(all_v[i], tr.p2), yocto::dot(all_v[i], tr.p3)});
      if (m > best_margin) { best_margin = m; best_ax = i; }
    }
    std::cout << "Triangle " << t << " [" << tr.name << "]: ";
    if (best_margin >= 0.0001) {
      std::cout << "COVERED by axis " << best_ax << " (margin " << best_margin << ")\n";
      fully_covered++;
    } else {
      std::cout << "FAILED (best margin " << best_margin << ")\n";
    }
  }

  std::cout << "\nRESULT: " << fully_covered << " / " << tris.size() << " triangles covered!\n";
  return 0;
}
