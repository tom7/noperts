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

  // 1. Collect certified certificates specifically from 031213
  std::vector<TubeCertificate> local_seeds;
  auto collect_seeds = [&](auto &self, TreeNode *node) -> void {
    if (!node || local_seeds.size() >= 1000) return;
    if (node->path.starts_with("031213") && node->direct_cert.has_value() &&
        BigRat::Sign(node->direct_cert->r) > 0) {
      local_seeds.push_back(*node->direct_cert);
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect_seeds(collect_seeds, root.get());
  std::cout << "Collected " << local_seeds.size() << " certified seeds from 031213.\n";

  // 2. Collect 1000 uncertified leaves from 03121303
  std::vector<TreeNode*> uncert;
  auto collect_uncert = [&](auto &self, TreeNode *node) -> void {
    if (!node || uncert.size() >= 1000) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) return;
    if (node->children.empty() && node->path.starts_with("03121303")) {
      uncert.push_back(node);
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect_uncert(collect_uncert, root.get());
  std::cout << "Collected " << uncert.size() << " uncertified leaves from 03121303.\n";

  // 3. Test audit against local seeds
  int audited_ok = 0;
  for (TreeNode *leaf : uncert) {
    TriangleQ tri = leaf->GetTriangle();
    for (const auto &seed : local_seeds) {
      TubeCertificate out_cert;
      if (Tube229::AuditCertificateAdaptive(tri, seed, &out_cert)) {
        audited_ok++;
        break;
      }
    }
  }

  std::cout << "Result: " << audited_ok << " / " << uncert.size() << " ("
            << (100.0 * audited_ok / uncert.size()) << "%) certified by local seeds!\n";

  return 0;
}
