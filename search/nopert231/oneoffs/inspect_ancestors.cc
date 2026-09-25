#include <iostream>
#include <vector>
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::string full_path = "031213002112122012121";

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
