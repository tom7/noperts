#include <iostream>
#include <string>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0.json.bak_dfs";
  std::cout << "Loading tree from " << file << "...\n" << std::flush;
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  if (!root) {
    std::cerr << "Failed to load tree.\n";
    return 1;
  }
  std::cout << "Loaded!\n" << std::flush;

  std::vector<std::string> paths = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  for (const auto &p : paths) {
    const TreeNode *node = root.get();
    for (size_t i = 1; i < p.size(); i++) {
      int idx = p[i] - '0';
      if (idx >= 0 && idx < (int)node->children.size() && node->children[idx]) {
        node = node->children[idx].get();
      } else {
        node = nullptr;
        break;
      }
    }
    if (!node) {
      std::cout << "Path " << p << " not found!\n";
      continue;
    }

    int total_nodes = 0;
    int cert_leaves = 0;
    int uncert_leaves = 0;
    int max_depth = 0;
    int min_uncert_depth = 999;
    int max_uncert_depth = 0;

    auto walk = [&](auto &self, const TreeNode &n, int depth) -> void {
      total_nodes++;
      if (depth > max_depth) max_depth = depth;
      if (n.children.empty()) {
        if (n.direct_cert.has_value() || BigRat::Sign(n.direct_bounds.direct_c_lower) > 0) {
          cert_leaves++;
        } else {
          uncert_leaves++;
          if (depth < min_uncert_depth) min_uncert_depth = depth;
          if (depth > max_uncert_depth) max_uncert_depth = depth;
        }
        return;
      }
      for (const auto &c : n.children) {
        if (c) self(self, *c, depth + 1);
      }
    };
    walk(walk, *node, p.size() - 1);

    std::cout << "\nPath " << p << " (depth " << p.size() - 1 << "):\n"
              << "  total nodes: " << total_nodes << "\n"
              << "  cert leaves: " << cert_leaves << "\n"
              << "  uncert leaves: " << uncert_leaves << "\n"
              << "  depth range: " << min_uncert_depth << " .. " << max_uncert_depth << "\n";
  }

  return 0;
}
