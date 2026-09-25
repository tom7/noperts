#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

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
  std::cout << "Valid contacts: " << valid_contacts.size() << "\n";

  vec3 sep_norm = {-0.401011, 0.483067, 0.778355};
  int a = 0; // replace in axis 0
  double best_dot = -2.0;
  Tube229::CandidateTriple best_cand;

  for (int replace_pos = 0; replace_pos < 3; replace_pos++) {
    for (const auto &c : valid_contacts) {
      ContactInfo test_contacts[3] = {sib_cert.axes[a].contacts[0], sib_cert.axes[a].contacts[1], sib_cert.axes[a].contacts[2]};
      test_contacts[replace_pos] = c;
      Tube229::CandidateTriple cand;
      if (Tube229::DoubleCheckAxis(tri1, test_contacts, &cand, 0.0)) {
        double d = yocto::dot(cand.normalized_a, sep_norm);
        if (d > best_dot) {
          best_dot = d;
          best_cand = cand;
        }
      }
    }
  }

  std::cout << std::setprecision(10);
  std::cout << "Best dot with sep_norm among 1-contact replacements: " << best_dot << "\n";
  if (best_dot > -2.0) {
    std::cout << "  norm_a = (" << best_cand.normalized_a.x << ", "
              << best_cand.normalized_a.y << ", " << best_cand.normalized_a.z << ")\n";
    std::cout << "  slack = " << best_cand.strict_slack << "\n";
  }

  return 0;
}
