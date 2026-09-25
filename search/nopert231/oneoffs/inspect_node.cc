#include <iostream>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  auto root = LoadTreeJson("ruperts/.artifacts/nopert229/tree_0.json", false, "ruperts/.artifacts/nopert229");
  std::string p0 = "031213002112122012120";
  TreeNode *n0 = nullptr;
  auto find_node = [&](auto &self, TreeNode *n) -> void {
    if (!n || n0) return;
    if (n->path == p0) { n0 = n; return; }
    if (p0.starts_with(n->path)) {
      for (auto &c : n->children) self(self, c.get());
    }
  };
  find_node(find_node, root.get());
  if (!n0) {
    std::cout << "Node not found!" << std::endl;
    return 1;
  }
  std::cout << "Node path: " << n0->path << std::endl;
  std::cout << "depth: " << n0->depth << std::endl;
  std::cout << "has direct_cert: " << (n0->direct_cert != nullptr) << std::endl;
  std::cout << "has tube_cert: " << (n0->tube_cert != nullptr) << std::endl;
  if (n0->direct_cert) {
    std::cout << "direct_cert c: " << n0->direct_cert->c << ", delta: " << n0->direct_cert->delta << ", r: " << n0->direct_cert->r << std::endl;
  }
  return 0;
}
