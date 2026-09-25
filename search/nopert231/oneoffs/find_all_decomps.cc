#include <iostream>
#include <vector>
#include <string>
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");

  std::vector<std::pair<std::string, int>> decomps;
  auto scan = [&](auto &self, TreeNode *n) -> void {
    if (n->decomposed_cert.has_value()) {
      decomps.push_back({n->path, (int)n->children.size()});
    }
    for (auto &c : n->children) self(self, c.get());
  };
  scan(scan, root.get());

  std::cout << "Total decomposed nodes in full tree: " << decomps.size() << "\n";
  for (const auto &p : decomps) {
    std::cout << "  path: " << p.first << ", children: " << p.second << "\n";
  }
  return 0;
}
