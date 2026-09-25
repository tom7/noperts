#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Real Annular Axis from tree_0.json
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c_ann, &cert0, &center0, &delta0, &err, BigRat(5, 1000));

  vec3 u0 = {center0.x.ToDouble() / cert0.B.ToDouble(),
             center0.y.ToDouble() / cert0.B.ToDouble(),
             center0.z.ToDouble() / cert0.B.ToDouble()};
  double u0_norm = yocto::length(u0);
  vec3 u0_hat = u0 / u0_norm;

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), norm: " << u0_norm << "\n";
  std::cout << "u0_hat: (" << u0_hat.x << ", " << u0_hat.y << ", " << u0_hat.z << ")\n";

  // Basis for orthogonal complement of u0
  vec3 e1 = yocto::normalize(yocto::cross(u0_hat, vec3{0, 1, 0}));
  vec3 e2 = yocto::normalize(yocto::cross(u0_hat, e1));

  double c_cone = 0.2;
  double R_disk = std::sqrt(1.0 - c_cone * c_cone);
  std::cout << "c_cone: " << c_cone << ", R_disk: " << R_disk << "\n";
  std::cout << "Cone aperture: " << std::acos(c_cone) * 180.0 / M_PI << " deg\n";

  // Load all audited zero-defect axes from our expanded contact pool
  std::vector<ContactInfo> known_contacts = {
    {15, 19, 19, 3, 200, 19},
    {2, 1, 1, 4, 200, 1},
    {8, 9, 9, 10, 200, 9},
    {2, 1, 1, 4, 0, 1},
    {10, 15, 15, 19, 333, 15},
    {10, 15, 15, 19, 0, 15},
    {3, 2, 2, 1, 800, 2},
    {4, 8, 8, 9, 800, 8},
    {14, 15, 15, 19, 800, 15},
    {14, 15, 15, 19, 500, 15},
    {2, 1, 1, 4, 500, 1}
  };
  struct PairDef { int v, s1, f1, s2, f2; };
  std::vector<PairDef> pairs;
  for (const auto &c : known_contacts) {
    bool dup = false;
    for (const auto &p : pairs) {
      if (p.v == c.vertex && p.s1 == c.edge_start && p.f1 == c.edge_finish &&
          p.s2 == c.edge_start2 && p.f2 == c.edge_finish2) {
        dup = true; break;
      }
    }
    if (!dup) pairs.push_back({c.vertex, c.edge_start, c.edge_finish, c.edge_start2, c.edge_finish2});
  }

  std::vector<ContactInfo> expanded_contacts;
  std::vector<int> test_mixes = {0, 100, 200, 333, 500, 666, 800, 900, 1000};
  for (const auto &p : pairs) {
    for (int m : test_mixes) {
      ContactInfo c;
      c.vertex = p.v;
      c.edge_start = p.s1; c.edge_finish = p.f1;
      c.edge_start2 = p.s2; c.edge_finish2 = p.f2;
      c.mix = m;
      expanded_contacts.push_back(c);
    }
  }

  std::vector<vec3> core_axes;
  for (size_t i = 0; i < expanded_contacts.size(); i++) {
    for (size_t j = i + 1; j < expanded_contacts.size(); j++) {
      for (size_t k = j + 1; k < expanded_contacts.size(); k++) {
        ContactInfo triple[3] = {expanded_contacts[i], expanded_contacts[j], expanded_contacts[k]};
        Tube229::CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        AxisCertificate cert;
        BigVecQ3 center;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &err, BigRat(0))) {
          vec3 a = yocto::normalize(vec3{center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
          core_axes.push_back(a);
        }
      }
    }
  }
  std::cout << "Audited zero-defect axes: " << core_axes.size() << "\n";

  for (int N = 6; N <= 48; N += 2) {
    double R_poly = R_disk / std::cos(M_PI / N);
    vec3 center_pt = c_cone * u0_hat;

    std::vector<vec3> poly_verts(N);
    for (int k = 0; k < N; k++) {
      double angle = 2.0 * M_PI * k / N;
      poly_verts[k] = center_pt + R_poly * (std::cos(angle) * e1 + std::sin(angle) * e2);
    }

    double c_core = 0.001;
    int covered_triangles = 0;
    for (int k = 0; k < N; k++) {
      vec3 v0 = center_pt;
      vec3 v1 = poly_verts[k];
      vec3 v2 = poly_verts[(k + 1) % N];

      bool tri_covered = false;
      for (const auto &ax : core_axes) {
        if (yocto::dot(v0, ax) >= c_core * yocto::length(v0) &&
            yocto::dot(v1, ax) >= c_core * yocto::length(v1) &&
            yocto::dot(v2, ax) >= c_core * yocto::length(v2)) {
          tri_covered = true;
          break;
        }
      }
      if (tri_covered) covered_triangles++;
    }
    std::cout << "N = " << N << ": covered triangles = " << covered_triangles << " / " << N << "\n";
  }

  return 0;
}
