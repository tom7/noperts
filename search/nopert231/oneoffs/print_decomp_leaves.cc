#include <iostream>
#include <string>
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false);
  if (!root) {
    std::cerr << "Failed to load " << file << "\n";
    return 1;
  }

  auto print_decomp = [](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->decomposed_cert.has_value()) {
      const auto &dc = *node->decomposed_cert;
      std::cout << "Path: " << node->path << " (depth " << node->depth() << ")\n";
      std::cout << "  r = " << dc.r.ToString() << " (" << dc.r.ToDouble() << ")\n";
      std::cout << "  r_min = " << dc.r_min.ToString() << " (" << dc.r_min.ToDouble() << ")\n";
      std::cout << "  c_cone = " << dc.c_cone.ToString() << " (" << dc.c_cone.ToDouble() << ")\n";
      std::cout << "  c_core = " << dc.c_core.ToString() << " (" << dc.c_core.ToDouble() << ")\n";
      std::cout << "  c_comp = " << dc.c_comp.ToString() << " (" << dc.c_comp.ToDouble() << ")\n";
      std::cout << "  delta = " << dc.delta.ToString() << " (" << dc.delta.ToDouble() << ")\n";
      std::cout << "  lam = " << dc.lam.ToString() << " (" << dc.lam.ToDouble() << ")\n";
      std::cout << "  w = [" << dc.w[0].ToString() << ", " << dc.w[1].ToString() << ", " << dc.w[2].ToString() << "]\n";
      std::cout << "  B0 = " << dc.annular_axis.B.ToString() << "\n";
      std::cout << "  B_core = " << dc.inner_core_axis.B.ToString() << "\n";
      std::cout << "  num_comp = " << dc.complement_axes.size() << "\n";

    }
    for (auto &c : node->children) self(self, c.get());
  };

  print_decomp(print_decomp, root.get());
  return 0;
}
