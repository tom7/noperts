#include <iostream>
#include <vector>
#include <map>
#include <string>
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::map<int, std::map<std::string, int>> depth_prefix_counts;
  auto collect = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->children.empty()) {
      if (!node->direct_cert.has_value() || BigRat::Sign(node->direct_cert->r) <= 0) {
        std::string pref = node->path.substr(0, std::min((size_t)8, node->path.size()));
        depth_prefix_counts[node->depth()][pref]++;
      }
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  std::cout << "Uncertified leaf prefixes by depth:\n";
  for (const auto &[d, pmap] : depth_prefix_counts) {
    std::cout << "Depth " << d << ":\n";
    for (const auto &[pref, count] : pmap) {
      std::cout << "  " << pref << ": " << count << " leaves\n";
    }
  }

  return 0;
}
