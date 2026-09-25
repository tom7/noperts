#include <iostream>
#include <vector>
#include <string>
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");

  std::vector<std::string> paths = {
    "03121300",
    "0312130332",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200"
  };

  for (const auto &p : paths) {
    TreeNode *node = nullptr;
    auto find = [&](auto &self, TreeNode *n) -> void {
      if (n->path == p) { node = n; return; }
      for (auto &c : n->children) self(self, c.get());
    };
    find(find, root.get());
    std::cout << "Path " << p << ":\n";
    if (!node) {
      std::cout << "  NOT FOUND!\n";
      continue;
    }
    std::cout << "  direct: " << node->direct_cert.has_value()
              << ", decomposed: " << node->decomposed_cert.has_value()
              << ", children: " << node->children.size() << "\n";
    if (node->direct_cert.has_value()) {
      std::cout << "  direct r: " << node->direct_cert->r.ToString() << "\n";
    }
    if (node->decomposed_cert.has_value()) {
      std::cout << "  decomposed r: " << node->decomposed_cert->r.ToString() << "\n";
    }
    for (size_t c = 0; c < node->children.size(); c++) {
      auto &ch = node->children[c];
      std::cout << "    child " << c << " (" << ch->path << "): direct="
                << ch->direct_cert.has_value() << ", decomposed="
                << ch->decomposed_cert.has_value() << ", ch_count="
                << ch->children.size() << "\n";
    }
  }

  return 0;
}
