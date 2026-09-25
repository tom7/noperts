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

  // 6 regular sectors of 45 deg
  for (int k = 0; k < 6; k++) {
    double phi1 = k * (M_PI / 4.0);
    double phi2 = (k + 1) * (M_PI / 4.0);
    vec3 b1 = std::sin(alpha) * (std::cos(phi1) * k1 + std::sin(phi1) * k2) + std::cos(alpha) * u0;
    vec3 b2 = std::sin(alpha) * (std::cos(phi2) * k1 + std::sin(phi2) * k2) + std::cos(alpha) * u0;
    tris.push_back({p0, b1, b2, "Sector " + std::to_string(k)});
  }

  // Subdivide [270, 360] into 8 subsectors (11.25 deg each)
  // And 2 intermediate radii: 48 deg, 64 deg
  int K_fine = 8;
  double r1 = 48.0 * M_PI / 180.0;
  double r2 = 64.0 * M_PI / 180.0;
  double r3 = alpha;

  auto get_pt = [&](double psi, double phi) {
    return std::sin(psi) * (std::cos(phi) * k1 + std::sin(phi) * k2) + std::cos(psi) * u0;
  };

  for (int j = 0; j < K_fine; j++) {
    double phi1 = (3.0 * M_PI / 2.0) + j * (M_PI / (2.0 * K_fine));
    double phi2 = (3.0 * M_PI / 2.0) + (j + 1) * (M_PI / (2.0 * K_fine));

    vec3 a1 = get_pt(r1, phi1), a2 = get_pt(r1, phi2);
    vec3 b1 = get_pt(r2, phi1), b2 = get_pt(r2, phi2);
    vec3 c1 = get_pt(r3, phi1), c2 = get_pt(r3, phi2);

    // Inner: (p0, a1, a2)
    tris.push_back({p0, a1, a2, "Canyon " + std::to_string(j) + " (inner)"});
    // Mid: (a1, b1, b2), (a1, a2, b2)
    tris.push_back({a1, b1, b2, "Canyon " + std::to_string(j) + " (mid 1)"});
    tris.push_back({a1, a2, b2, "Canyon " + std::to_string(j) + " (mid 2)"});
    // Outer: (b1, c1, c2), (b1, b2, c2)
    tris.push_back({b1, c1, c2, "Canyon " + std::to_string(j) + " (outer 1)"});
    tris.push_back({b1, b2, c2, "Canyon " + std::to_string(j) + " (outer 2)"});
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
    if (best_margin >= 0.0001) {
      fully_covered++;
    } else {
      std::cout << "Triangle " << t << " [" << tr.name << "] FAILED (best margin " << best_margin << ")\n";
    }
  }

  std::cout << "\nRESULT: " << fully_covered << " / " << tris.size() << " triangles covered!\n";
  return 0;
}
