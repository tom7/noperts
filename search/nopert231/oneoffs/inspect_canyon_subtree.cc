#include <iostream>
#include <vector>
#include <string>
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");

  TreeNode *target = nullptr;
  auto find = [&](auto &self, TreeNode *n) -> void {
    if (n->path == "03121300") { target = n; return; }
    for (auto &c : n->children) self(self, c.get());
  };
  find(find, root.get());

  int total_leaves = 0;
  int direct_leaves = 0;
  int decomp_leaves = 0;
  int uncertified_leaves = 0;

  auto count_leaves = [&](auto &self, TreeNode *n) -> void {
    if (n->children.empty()) {
      total_leaves++;
      if (n->decomposed_cert.has_value()) {
        decomp_leaves++;
        std::cout << "Decomposed leaf: " << n->path << ", r=" << n->decomposed_cert->r.ToString() << "\n";
      } else if (n->direct_cert.has_value()) {
        direct_leaves++;
      } else {
        uncertified_leaves++;
        std::cout << "UNCERTIFIED leaf: " << n->path << "\n";
      }
      return;
    }
    for (auto &c : n->children) self(self, c.get());
  };

  count_leaves(count_leaves, target);
  std::cout << "Subtree 03121300:\n"
            << "  total leaves: " << total_leaves << "\n"
            << "  direct leaves: " << direct_leaves << "\n"
            << "  decomp leaves: " << decomp_leaves << "\n"
            << "  uncertified: " << uncertified_leaves << "\n";

  return 0;
}
