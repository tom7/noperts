#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);

  // Annular axis u0:
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  // Filter valid zero-defect axes:
  std::vector<vec3> zero_defect_dirs;
  std::vector<int> zero_defect_indices;
  for (size_t a = 0; a < axes500.size(); a++) {
    ContactInfo triple[3] = {axes500[a].cert.contacts[0], axes500[a].cert.contacts[1], axes500[a].cert.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    if (Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &fail, BigRat(0))) {
      zero_defect_dirs.push_back({center.x.ToDouble() / cert.B.ToDouble(),
                                 center.y.ToDouble() / cert.B.ToDouble(),
                                 center.z.ToDouble() / cert.B.ToDouble()});
      zero_defect_indices.push_back(a);
    }
  }

  std::cout << "Valid zero-defect axes: " << zero_defect_dirs.size() << "\n";

  // Sample 200,000 points on sphere:
  double c_min = 0.0041195;
  double c_max = 0.035;
  std::vector<vec3> annulus_pts;
  int N = 200000;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double d0 = yocto::dot(a, u0);
    if (d0 >= c_min && d0 <= c_max) {
      annulus_pts.push_back(a);
    }
  }

  std::cout << "Points in annulus: " << annulus_pts.size() << "\n";

  // Find 1 or 2 axes among zero_defect_dirs that maximize minimum coverage on annulus:
  // First test single axes:
  double best_single_cover = -1e9;
  int best_single_idx = -1;
  for (size_t i = 0; i < zero_defect_dirs.size(); i++) {
    double min_d = 1e9;
    for (const auto &pt : annulus_pts) {
      double d = yocto::dot(pt, zero_defect_dirs[i]);
      if (d < min_d) min_d = d;
    }
    if (min_d > best_single_cover) {
      best_single_cover = min_d;
      best_single_idx = i;
    }
  }
  std::cout << "Best single axis cover on annulus: " << best_single_cover
            << " (index " << zero_defect_indices[best_single_idx] << ")\n";

  // Test pairs:
  double best_pair_cover = -1e9;
  int best_i = -1, best_j = -1;
  for (size_t i = 0; i < std::min((size_t)100, zero_defect_dirs.size()); i++) {
    for (size_t j = i + 1; j < std::min((size_t)100, zero_defect_dirs.size()); j++) {
      double min_d = 1e9;
      for (const auto &pt : annulus_pts) {
        double d = std::max(yocto::dot(pt, zero_defect_dirs[i]), yocto::dot(pt, zero_defect_dirs[j]));
        if (d < min_d) min_d = d;
      }
      if (min_d > best_pair_cover) {
        best_pair_cover = min_d;
        best_i = i; best_j = j;
      }
    }
  }
  std::cout << "Best pair cover on annulus: " << best_pair_cover
            << " (indices " << zero_defect_indices[best_i] << ", " << zero_defect_indices[best_j] << ")\n";

  return 0;
}
