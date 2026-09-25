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
  if (!target || !target->decomposed_cert.has_value()) {
    std::cout << "target not found or no decomposed_cert\n";
    return 1;
  }

  const auto &dec = *target->decomposed_cert;
  std::cout << "Path: 03121300\n";
  std::cout << "r = " << dec.r.ToString() << "\n";
  std::cout << "c_comp = " << dec.c_comp.ToString() << "\n";
  std::cout << "c_cone = " << dec.c_cone.ToString() << "\n";
  std::cout << "c_core = " << dec.c_core.ToString() << "\n";
  std::cout << "r_min = " << dec.r_min.ToString() << "\n";
  std::cout << "delta = " << dec.delta.ToString() << "\n";
  std::cout << "defect_D = " << dec.defect_D.ToString() << "\n";
  std::cout << "defect0 = [" << dec.defect0[0].ToString() << ", " << dec.defect0[1].ToString() << ", " << dec.defect0[2].ToString() << "]\n";
  std::cout << "lambda = " << dec.lam.ToString() << "\n";
  std::cout << "w = (" << dec.w[0].ToString() << ", " << dec.w[1].ToString() << ", " << dec.w[2].ToString() << ")\n";
  std::cout << "Complement axes count: " << dec.complement_axes.size() << "\n";
  for (size_t a = 0; a < dec.complement_axes.size(); a++) {
    std::cout << "  Comp axis " << a << " B=" << dec.complement_axes[a].B.ToString() << "\n";
    for (int c = 0; c < 3; c++) {
      const auto &ct = dec.complement_axes[a].contacts[c];
      std::cout << "    Contact " << c << ": (" << ct.edge_start << "->" << ct.edge_finish << ", "
                << ct.edge_start2 << "->" << ct.edge_finish2 << ", mix=" << ct.mix << ", v=" << ct.vertex << ")\n";
    }
  }

  return 0;
}
