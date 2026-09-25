#include <random>
#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Complement axes from tree_0.json
  ContactInfo c_comp[3][3] = {
    { {15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9} },
    { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {8, 9, 9, 10, 200, 9} },
    { {10, 15, 15, 19, 0, 15}, {3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8} }
  };

  std::vector<vec3> audited_axes;
  // Add complement axes
  for (int j = 0; j < 3; j++) {
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    if (Tube229::AuditAxis(tri, c_comp[j], &cert, &center, &delta, &err, BigRat(0))) {
      vec3 a = yocto::normalize(vec3{center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
      audited_axes.push_back(a);
      std::cout << "Comp " << j << ": (" << a.x << ", " << a.y << ", " << a.z << ")\n";
    }
  }

  // Load known contacts and generate zero-defect core axes
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
          audited_axes.push_back(a);
        }
      }
    }
  }
  std::cout << "Total audited zero-defect axes (comp + core): " << audited_axes.size() << "\n";

  // Check sphere coverage: for 500,000 random unit vectors on S^2, what is max dot?
  std::mt19937_64 rng(42);
  std::normal_distribution<double> dist(0.0, 1.0);
  double min_max_dot = 1.0;
  int uncovered = 0;
  double target_c = 0.001; // target inradius

  for (int s = 0; s < 500000; s++) {
    vec3 v = {dist(rng), dist(rng), dist(rng)};
    v = yocto::normalize(v);
    double max_dot = -1.0;
    for (const auto &a : audited_axes) {
      double d = yocto::dot(v, a);
      if (d > max_dot) max_dot = d;
    }
    if (max_dot < min_max_dot) min_max_dot = max_dot;
    if (max_dot < target_c) uncovered++;
  }

  std::cout << "Sphere coverage over 500,000 samples:\n";
  std::cout << "Min max dot across sphere = " << min_max_dot << "\n";
  std::cout << "Uncovered samples (< " << target_c << ") = " << uncovered << " / 500000\n";

  return 0;
}
