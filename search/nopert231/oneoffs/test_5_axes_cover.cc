#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>

#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

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
  const TubeCertificate &c0 = *n0->direct_cert;

  // Sibling axes 1, 2, 3 are strictly valid on tri1:
  std::vector<Tube229::CandidateTriple> valid_axes;
  for (int a = 1; a < 4; a++) {
    Tube229::CandidateTriple cand;
    if (Tube229::DoubleCheckAxis(tri1, c0.axes[a].contacts, &cand, 0.0)) {
      valid_axes.push_back(cand);
    }
  }
  std::cout << "Valid sibling axes on tri1: " << valid_axes.size() << "\n";

  // Now synthesize candidate axes on tri1
  std::vector<Tube229::CandidateTriple> pool;
  TubeCertificate dummy;
  // Let's generate candidates on tri1 using rich sampling
  Tube229::SynthesizeCertificateIterative(tri1, 21, &dummy);
  
  return 0;
}
