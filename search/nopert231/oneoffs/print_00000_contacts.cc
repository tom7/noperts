#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  TreeNode *found = nullptr;
  auto dfs = [&](auto &self, TreeNode *node) -> void {
    if (found) return;
    if (node->path == "00000") { found = node; return; }
    for (auto &c : node->children) self(self, c.get());
  };
  dfs(dfs, root.get());
  if (!found || !found->direct_cert) return 1;

  const TubeCertificate &cert = *found->direct_cert;
  for (int a = 0; a < 4; a++) {
    std::cout << "// Axis " << a << "\n";
    for (int c = 0; c < 3; c++) {
      const auto &ct = cert.axes[a].contacts[c];
      std::cout << "MakeContact(" << ct.edge_start << ", " << ct.edge_finish << ", "
                << ct.edge_start2 << ", " << ct.edge_finish2 << ", "
                << ct.mix << ", " << ct.vertex << "),\n";
    }
  }
  return 0;
}
