#include <iostream>
#include <iomanip>
#include <string>
#include <map>
#include <vector>
#include "tubetree229.h"

using namespace tubetree229;

void InspectSubtree(TreeNode *node, int target_depth, int current_depth = 0) {
  if (!node) return;
  if (current_depth == target_depth) {
    bool has_c = node->has_certificate();
    bool has_children = !node->children.empty();
    std::cout << "Node " << node->path << ": "
              << (has_c ? "CERTIFIED (r=" + node->GetCertifiedRadius().ToString() + ")" : "UNCERTIFIED")
              << ", children=" << node->children.size() << "\n";
    return;
  }
  for (auto &c : node->children) {
    InspectSubtree(c.get(), target_depth, current_depth + 1);
  }
}

int main(int argc, char **argv) {
  std::string file = ".artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false);
  if (!root) return 1;

  // Find node 0312130
  std::string target = "0312130";
  TreeNode *curr = root.get();
  for (size_t i = 1; i < target.size(); i++) {
    int idx = target[i] - '0';
    if (idx < 0 || idx >= (int)curr->children.size()) {
      std::cerr << "Path broken at index " << i << " char " << target[i]
                << " (current node path " << curr->path << " has "
                << curr->children.size() << " children)\n";
      return 1;
    }
    curr = curr->children[idx].get();
  }

  std::cout << "Found node " << curr->path << " (depth " << curr->depth() << ")\n";
  std::cout << "Children count: " << curr->children.size() << "\n";
  for (size_t i = 0; i < curr->children.size(); i++) {
    auto *child = curr->children[i].get();
    std::cout << "  Child " << i << " (" << child->path << "): "
              << (child->has_certificate() ? "CERTIFIED" : "UNCERTIFIED")
              << ", children=" << child->children.size() << "\n";
  }

  std::cout << "\nInspecting depths 8 to 15 under 0312130:\n";
  for (int d = 1; d <= 7; d++) {
    std::cout << "--- Relative depth " << d << " (absolute depth " << (7 + d) << ") ---\n";
    InspectSubtree(curr, d);
  }

  return 0;
}
