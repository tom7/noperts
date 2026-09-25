#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct RayTri {
  vec3 q[3];
};

static RayTri SplitTri(const RayTri &t, int child) {
  vec3 m01 = t.q[0] + t.q[1];
  vec3 m12 = t.q[1] + t.q[2];
  vec3 m20 = t.q[2] + t.q[0];
  switch (child) {
    case 0: return {t.q[0], m01, m20};
    case 1: return {m01, t.q[1], m12};
    case 2: return {m20, m12, t.q[2]};
    case 3: return {m01, m12, m20};
  }
  return t;
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Annular axis u0
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c_ann, &cert0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()});

  double c_cone = 0.2;
  double c_core = 0.001;

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
  std::vector<AxisCertificate> core_certs;

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
          if (yocto::dot(a, u0) > 0.1) {
            bool dup = false;
            for (const auto &ex : core_axes) {
              if (yocto::dot(a, ex) > 0.9999) { dup = true; break; }
            }
            if (!dup) {
              core_axes.push_back(a);
              core_certs.push_back(cert);
            }
          }
        }
      }
    }
  }
  std::cout << "Collected " << core_axes.size() << " unique zero-defect core axes with dot(a, u0) > 0.1\n";

  // Build the bounding polygon around the circular cone in the plane <x, u0> = c_cone
  vec3 e1 = yocto::normalize(yocto::cross(u0, vec3{0, 1, 0}));
  vec3 e2 = yocto::normalize(yocto::cross(u0, e1));
  double R_disk = std::sqrt(1.0 - c_cone * c_cone);

  // We test N = 8, 12, 16, 24
  for (int N : {8, 12, 16, 24}) {
    double R_poly = R_disk / std::cos(M_PI / N);
    vec3 center_pt = c_cone * u0;
    std::vector<vec3> poly_verts(N);
    for (int k = 0; k < N; k++) {
      double angle = 2.0 * M_PI * k / N;
      poly_verts[k] = center_pt + R_poly * (std::cos(angle) * e1 + std::sin(angle) * e2);
    }

    struct Node {
      RayTri tri;
      int depth;
    };
    std::vector<Node> stack;
    for (int k = 0; k < N; k++) {
      stack.push_back({{center_pt, poly_verts[k], poly_verts[(k + 1) % N]}, 0});
    }

    int total_leaves = 0;
    int max_depth = 0;
    bool failed = false;
    std::vector<int> used_axis_counts(core_axes.size(), 0);

    while (!stack.empty()) {
      Node node = stack.back();
      stack.pop_back();
      max_depth = std::max(max_depth, node.depth);

      int covered_by = -1;
      for (size_t a = 0; a < core_axes.size(); a++) {
        const auto &ax = core_axes[a];
        bool ok = true;
        for (int v = 0; v < 3; v++) {
          if (yocto::dot(node.tri.q[v], ax) < c_core * yocto::length(node.tri.q[v])) {
            ok = false; break;
          }
        }
        if (ok) {
          covered_by = (int)a;
          break;
        }
      }

      if (covered_by >= 0) {
        total_leaves++;
        used_axis_counts[covered_by]++;
      } else {
        if (node.depth >= 6) {
          failed = true;
          break;
        }
        for (int child = 0; child < 4; child++) {
          stack.push_back({SplitTri(node.tri, child), node.depth + 1});
        }
      }
    }

    if (!failed) {
      int unique_used = 0;
      for (int c : used_axis_counts) if (c > 0) unique_used++;
      std::cout << "SUCCESS for N=" << N << "! Tree closed with " << total_leaves
                << " leaves, max depth " << max_depth << ", using " << unique_used << " unique axes.\n";
      break;
    } else {
      std::cout << "N=" << N << " reached max depth without closing.\n";
    }
  }

  return 0;
}
