#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  std::vector<vec3> pool;
  int N = 80;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto candidates = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : candidates) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        BigVecQ3 u_ex = center / cert.B;
        vec3 u_vec = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
        pool.push_back(yocto::normalize(u_vec));
      }
    }
  }

  std::cout << "Harvested " << pool.size() << " normalized zero-defect vectors.\n";

  // Check if for a fine sphere grid, max_{u in pool} (v . u) is always strictly positive:
  int test_N = 5000;
  double min_max_dot = 1.0;
  vec3 worst_v = {0,0,0};
  for (int i = 0; i < test_N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / test_N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    double max_dot = -1.0;
    for (const auto& u : pool) {
      double d = yocto::dot(v, u);
      if (d > max_dot) max_dot = d;
    }
    if (max_dot < min_max_dot) {
      min_max_dot = max_dot;
      worst_v = v;
    }
  }

  std::cout << "min_max_dot = " << min_max_dot << "\n";
  if (min_max_dot > 0.0) {
    std::cout << "Origin is in the STRICT INTERIOR of the convex hull of zero-defect axes!\n";
  } else {
    std::cout << "Separating direction found: worst_v = (" << worst_v.x << ", " << worst_v.y << ", " << worst_v.z << ")\n";
  }
  return 0;
}
