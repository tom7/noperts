#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  if (!root) return 1;

  int total_leaves = 0;
  int certified_leaves = 0;
  std::vector<std::string> uncert;

  auto dfs = [&](auto &self, TreeNode *node) -> void {
    if (node->children.empty()) {
      total_leaves++;
      if (node->direct_cert.has_value() || node->decomposed_cert.has_value()) {
        certified_leaves++;
      } else {
        uncert.push_back(node->path);
      }
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  dfs(dfs, root.get());

  std::cout << "Total leaves: " << total_leaves << "\n";
  std::cout << "Certified leaves: " << certified_leaves << "\n";
  std::cout << "Uncertified leaves: " << uncert.size() << "\n";
  for (const auto &p : uncert) {
    std::cout << "  " << p << "\n";
  }

  return 0;
}
