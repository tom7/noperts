#include <iostream>
#include <vector>
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  // Find a leaf under 03121303
  TreeNode *target_leaf = nullptr;
  auto find_leaf = [&](auto &self, TreeNode *node) -> void {
    if (!node || target_leaf) return;
    if (node->depth() == 21 && node->children.empty() && !node->external &&
        node->path.starts_with("03121303")) {
      target_leaf = node;
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  find_leaf(find_leaf, root.get());

  if (!target_leaf) {
    std::cout << "No leaf found under 03121303\n";
    return 1;
  }

  std::string full_path = target_leaf->path;
  std::cout << "Target leaf: " << full_path << "\n";

  for (size_t len = 1; len <= full_path.size(); len++) {
    std::string prefix = full_path.substr(0, len);
    TreeNode *found = nullptr;
    auto search = [&](auto &self, TreeNode *node) -> void {
      if (!node) return;
      if (node->path == prefix) { found = node; return; }
      if (prefix.starts_with(node->path)) {
        for (auto &c : node->children) self(self, c.get());
      }
    };
    search(search, root.get());

    if (found) {
      std::cout << "Depth " << found->depth() << " (" << found->path << "): "
                << (found->direct_cert.has_value() ? "CERTIFIED" : "UNCERTIFIED")
                << " children=" << found->children.size()
                << " bounds=[r=" << found->direct_bounds.direct_r_lower.ToDouble() << ", " << found->direct_bounds.direct_r_upper.ToDouble() << "]\n";
    }
  }

  return 0;
}
