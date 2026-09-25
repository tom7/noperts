#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  int count = 0;
  auto dfs = [&](auto &self, TreeNode *node) -> void {
    if (node->direct_cert.has_value() && node->path.starts_with("031213")) {
      std::cout << "Certified node: " << node->path << "\n";
      count++;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  dfs(dfs, root.get());
  std::cout << "Total certified under 031213: " << count << "\n";
  return 0;
}
