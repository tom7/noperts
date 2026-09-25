#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>
#include <algorithm>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

// Solves barycentric coordinates for 0 in tetrahedron (p0, p1, p2, p3):
// sum_{i=0}^3 w_i * p_i = 0, sum w_i = 1.
// Returns min(w_i). If min(w_i) > 0, 0 is strictly inside the tetrahedron!
double BarycentricMin(vec3 p0, vec3 p1, vec3 p2, vec3 p3) {
  // Linear system:
  // (p0 - p3) * w0 + (p1 - p3) * w1 + (p2 - p3) * w2 = -p3
  vec3 a = p0 - p3;
  vec3 b = p1 - p3;
  vec3 c = p2 - p3;
  double det = yocto::dot(a, yocto::cross(b, c));
  if (std::abs(det) < 1e-15) return -1.0;

  vec3 rhs = -p3;
  double w0 = yocto::dot(rhs, yocto::cross(b, c)) / det;
  double w1 = yocto::dot(a, yocto::cross(rhs, c)) / det;
  double w2 = yocto::dot(a, yocto::cross(b, rhs)) / det;
  double w3 = 1.0 - w0 - w1 - w2;

  return std::min({w0, w1, w2, w3});
}

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::string p0 = "031213002112122012120";
  std::string p1 = "031213002112122012121";

  TreeNode *n0 = nullptr, *n1 = nullptr;
  auto find_nodes = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p0) n0 = node;
    if (node->path == p1) n1 = node;
    if (n0 && n1) return;
    if (p0.starts_with(node->path) || p1.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find_nodes(find_nodes, root.get());

  TriangleQ tri1 = TriangleFromPath(p1);
  const TubeCertificate &sib_cert = *n0->direct_cert;

  vec3 tri1_f[3] = {
    ToDouble(tri1.corners[0]),
    ToDouble(tri1.corners[1]),
    ToDouble(tri1.corners[2]),
  };

  std::vector<Tube229::CandidateTriple> valid_sibling_axes;
  for (int a = 1; a < 4; a++) {
    Tube229::CandidateTriple cand;
    Tube229::DoubleCheckAxis(tri1, sib_cert.axes[a].contacts, &cand);
    valid_sibling_axes.push_back(cand);
  }

  // Find all silhouette contacts from the tree that are valid across tri1
  std::vector<ContactInfo> valid_contacts;
  for (int v = 0; v < 20; v++) {
    for (int es = 0; es < 20; es++) {
      for (int ef = 0; ef < 20; ef++) {
        if (es == ef) continue;
        for (int mix : {0, 200, 333, 500, 667, 800, 1000}) {
          ContactInfo c = {v, es, ef, es, ef, mix};
          vec3 edge = Tube229::GetDoubleEdge(c);
          bool valid = true;
          for (int k = 0; k < 20; k++) {
            if (k == v) continue;
            vec3 delta = Tube229::Vertex(k) - Tube229::Vertex(v);
            vec3 coeff = yocto::cross(edge, delta);
            for (int corner = 0; corner < 3; corner++) {
              if (yocto::dot(tri1_f[corner], coeff) > 2e-14) {
                valid = false;
                break;
              }
            }
            if (!valid) break;
          }
          if (valid) valid_contacts.push_back(c);
        }
      }
    }
  }

  int a = 0;
  std::vector<Tube229::CandidateTriple> rep_axes;
  for (int replace_pos = 0; replace_pos < 3; replace_pos++) {
    for (const auto &c : valid_contacts) {
      ContactInfo test_contacts[3] = {sib_cert.axes[a].contacts[0], sib_cert.axes[a].contacts[1], sib_cert.axes[a].contacts[2]};
      test_contacts[replace_pos] = c;
      Tube229::CandidateTriple cand;
      if (Tube229::DoubleCheckAxis(tri1, test_contacts, &cand)) {
        rep_axes.push_back(cand);
      }
    }
  }

  vec3 p0_pt = valid_sibling_axes[0].normalized_a;
  vec3 p1_pt = valid_sibling_axes[1].normalized_a;
  vec3 p2_pt = valid_sibling_axes[2].normalized_a;

  std::cout << std::setprecision(10);
  std::cout << "Testing tetrahedra {Axis 1, Axis 2, Axis 3, rep_i}:\n";
  double best_w_min = -1.0;
  int best_i = -1;
  for (size_t i = 0; i < rep_axes.size(); i++) {
    vec3 p3_pt = rep_axes[i].normalized_a;
    double w_min = BarycentricMin(p0_pt, p1_pt, p2_pt, p3_pt);
    if (w_min > best_w_min) {
      best_w_min = w_min;
      best_i = i;
    }
  }

  std::cout << "Best barycentric min weight: " << best_w_min << " at rep " << best_i << "\n";
  if (best_w_min > 0) {
    std::cout << "SUCCESS! Tetrahedron STRICTLY CONTAINS ORIGIN!\n";
  }

  // Also test pairs of replacement axes: 5-axis convex hull!
  // In a 5-axis convex hull, 0 is contained iff some 4-element subset contains 0.
  // But more generally, let's test if 0 is in conv(p0, p1, p2, rep_i, rep_j):
  std::cout << "\nTesting 5-axis combinations (Axis 1, Axis 2, Axis 3, rep_i, rep_j):\n";
  // A 5-point set contains 0 iff 0 is in the convex hull of some 4 points,
  // OR we can solve the 5-variable LP / linear algebra:
  // sum_{k=0}^4 w_k p_k = 0, sum w_k = 1, w_k >= 0.
  // By Caratheodory's theorem, 0 in conv(5 points in R3) ==> 0 in conv(4 points in R3)!
  // So testing all 4-subsets of the 5 points suffices!

  return 0;
}
