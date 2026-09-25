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
  if (!target || !target->decomposed_cert.has_value()) return 1;

  const auto &dec = *target->decomposed_cert;
  std::cout << "Annular axis B=" << dec.annular_axis.B.ToString() << "\n";
  for (int c = 0; c < 3; c++) {
    const auto &ct = dec.annular_axis.contacts[c];
    std::cout << "  Contact " << c << ": (" << ct.edge_start << "->" << ct.edge_finish << ", "
              << ct.edge_start2 << "->" << ct.edge_finish2 << ", mix=" << ct.mix << ", v=" << ct.vertex << ")\n";
  }
  return 0;
}
