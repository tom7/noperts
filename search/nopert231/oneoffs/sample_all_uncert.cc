#include <iostream>
#include <vector>
#include <string>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::vector<TreeNode*> uncert;
  auto collect = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) return;
    if (node->children.empty()) {
      uncert.push_back(node);
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  std::cout << "Total uncertified leaves: " << uncert.size() << "\n";
  // Sample 200 evenly spaced leaves
  int n_samples = 200;
  int step = uncert.size() / n_samples;
  int fast_ok_count = 0;
  int fast_fail_count = 0;

  for (int i = 0; i < n_samples; i++) {
    TreeNode *leaf = uncert[i * step];
    TriangleQ tri = leaf->GetTriangle();
    TubeCertificate cert;
    if (Tube229::SynthesizeCertificateFast(tri, leaf->depth(), &cert)) {
      fast_ok_count++;
    } else {
      fast_fail_count++;
    }
  }

  std::cout << "Sample results (" << n_samples << " leaves evenly sampled):\n";
  std::cout << "  Fast certifiable: " << fast_ok_count << " (" << (100.0 * fast_ok_count / n_samples) << "%)\n";
  std::cout << "  Fast failed (seam): " << fast_fail_count << " (" << (100.0 * fast_fail_count / n_samples) << "%)\n";

  return 0;
}
