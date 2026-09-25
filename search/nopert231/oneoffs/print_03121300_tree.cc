#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  TreeNode *target = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (node->path == "03121300") { target = node; return; }
    for (auto &c : node->children) self(self, c.get());
  };
  find(find, root.get());
  if (!target) { std::cout << "target not found\n"; return 1; }

  std::cout << "Target node 03121300 has " << target->children.size() << " children.\n";
  for (size_t i = 0; i < target->children.size(); i++) {
    const auto &c = target->children[i];
    std::cout << "  Child " << i << ": path=" << c->path
              << ", is_leaf=" << (c->children.empty() ? "yes" : "no")
              << ", direct_cert=" << (c->direct_cert.has_value() ? "yes" : "no")
              << ", decomp_cert=" << (c->decomposed_cert.has_value() ? "yes" : "no") << "\n";
  }
  return 0;
}
