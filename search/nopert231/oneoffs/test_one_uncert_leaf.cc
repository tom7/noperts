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
    if (!node || uncert.size() >= 5) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) return;
    if (node->children.empty() && node->path.starts_with("03121303")) {
      uncert.push_back(node);
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  std::cout << "Found " << uncert.size() << " uncertified leaves under 03121303.\n";
  for (size_t i = 0; i < uncert.size(); i++) {
    TreeNode *leaf = uncert[i];
    std::cout << "\n--- Leaf " << i << ": path=" << leaf->path << " depth=" << leaf->depth() << " ---\n";
    TriangleQ tri = leaf->GetTriangle();

    // Try fast synthesis
    TubeCertificate fast_cert;
    bool fast_ok = Tube229::SynthesizeCertificateFast(tri, leaf->depth(), &fast_cert);
    std::cout << "Fast synthesis: " << (fast_ok ? "SUCCESS" : "FAILED") << "\n";

    // Try iterative synthesis
    TubeCertificate iter_cert;
    bool iter_ok = Tube229::SynthesizeCertificateIterative(tri, leaf->depth(), &iter_cert);
    std::cout << "Iterative synthesis: " << (iter_ok ? "SUCCESS" : "FAILED") << "\n";
  }

  return 0;
}
