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

  // Annular axis from tree_0.json:
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c_cone = 0.2; // 1/5

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), c_cone = " << c_cone << "\n";

  // Known contacts:
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

  std::vector<vec3> zero_axes;
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
          zero_axes.push_back(a);
        }
      }
    }
  }

  std::cout << "Audited zero axes: " << zero_axes.size() << "\n";

  // Test cone coverage using 500,000 points sampled in the cone:
  double c_core_target = 0.001; // target c_core
  int N = 500000;
  int uncovered = 0;
  double min_max_dot = 1e9;
  for (int i = 0; i < N; i++) {
    // Sample point uniformly in spherical cap:
    // z in [c_cone, 1.0]
    double z = c_cone + (1.0 - c_cone) * (double)i / (double)N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    // Cap centered at z-axis, then rotate to u0:
    vec3 local_pt = {r * std::cos(phi), r * std::sin(phi), z};
    // Basis around u0:
    vec3 up = std::abs(u0.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
    vec3 e1 = yocto::normalize(yocto::cross(u0, up));
    vec3 e2 = yocto::cross(u0, e1);
    vec3 a = yocto::normalize(local_pt.x * e1 + local_pt.y * e2 + local_pt.z * u0);

    double max_dot = -1e9;
    for (const auto &v : zero_axes) {
      double d = yocto::dot(a, v);
      if (d > max_dot) max_dot = d;
      if (max_dot >= c_core_target) break; // early exit
    }
    if (max_dot < min_max_dot) min_max_dot = max_dot;
    if (max_dot < c_core_target) {
      uncovered++;
    }
  }

  std::cout << "Target c_core = " << c_core_target << "\n";
  std::cout << "Uncovered points in cone: " << uncovered << " / " << N << "\n";
  std::cout << "Minimum max dot across all sampled cone points: " << min_max_dot << "\n";

  return 0;
}
