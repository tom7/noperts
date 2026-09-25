#include <iostream>
#include <vector>
#include <unordered_map>
#include <map>
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::map<std::string, int> prefix_counts;
  auto collect = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) return;
    if (node->depth() == 21 && node->children.empty() && !node->external) {
      std::string pref = node->path.substr(0, std::min((size_t)8, node->path.size()));
      prefix_counts[pref]++;
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  std::cout << "Prefix distribution of uncertified depth-21 leaves:\n";
  for (const auto &[pref, count] : prefix_counts) {
    std::cout << "  Prefix " << pref << ": " << count << " leaves\n";
  }

  return 0;
}
