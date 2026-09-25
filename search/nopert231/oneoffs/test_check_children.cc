#include <iostream>
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

  std::cout << "Node " << target->path << ":\n";
  std::cout << "  has direct_cert: " << target->direct_cert.has_value() << "\n";
  std::cout << "  has decomposed_cert: " << target->decomposed_cert.has_value() << "\n";
  std::cout << "  children count: " << target->children.size() << "\n";

  for (size_t c = 0; c < target->children.size(); c++) {
    auto &ch = target->children[c];
    std::cout << "  Child " << c << " (" << ch->path << "):\n";
    std::cout << "    has direct_cert: " << ch->direct_cert.has_value() << "\n";
    std::cout << "    has decomposed_cert: " << ch->decomposed_cert.has_value() << "\n";
    std::cout << "    children count: " << ch->children.size() << "\n";
    if (ch->direct_cert.has_value()) {
      std::cout << "    direct_cert r = " << ch->direct_cert->r.ToString() << "\n";
    }
    if (ch->decomposed_cert.has_value()) {
      std::cout << "    decomposed_cert r = " << ch->decomposed_cert->r.ToString() << "\n";
    }
  }

  return 0;
}
