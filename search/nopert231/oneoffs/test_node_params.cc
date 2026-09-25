#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "tubetree229.h"

using namespace tubetree229;

const TreeNode* FindPath(const TreeNode &node, const std::string &target) {
  if (node.path == target) return &node;
  for (int c = 0; c < 4; c++) {
    if (c < (int)node.children.size() && node.children[c]) {
      const auto *res = FindPath(*node.children[c], target);
      if (res) return res;
    }
  }
  return nullptr;
}

int main() {
  std::string json_path = "/home/tom/nopert-project/Noperthedron/.artifacts/nopert229/local-view-child0.json";
  auto tree = LoadTreeJson(json_path);
  std::string target = "03121303200";
  const auto *node = FindPath(*tree, target);
  if (!node) {
    std::cout << "Node " << target << " not found!\n";
    return 1;
  }
  std::cout << "Found node " << target << "!\n";
  std::cout << "has_certificate = " << node->has_certificate() << "\n";
  std::cout << "has direct_cert = " << node->direct_cert.has_value() << "\n";
  std::cout << "has decomposed_cert = " << node->decomposed_cert.has_value() << "\n";
  if (node->decomposed_cert.has_value()) {
    const auto &d = *node->decomposed_cert;
    std::cout << "c_cone = " << d.c_cone.ToDouble() << "\n";
    std::cout << "c_core = " << d.c_core.ToDouble() << "\n";
    std::cout << "r_min = " << d.r_min.ToDouble() << "\n";
    std::cout << "c_comp = " << d.c_comp.ToDouble() << "\n";
    std::cout << "delta = " << d.delta.ToDouble() << "\n";
    std::cout << "r = " << d.r.ToDouble() << "\n";
    std::cout << "defect_D = " << d.defect_D.ToDouble() << "\n";
    std::cout << "defect0 = [" << d.defect0[0].ToDouble() << ", "
                               << d.defect0[1].ToDouble() << ", "
                               << d.defect0[2].ToDouble() << "]\n";
    std::cout << "inner_core_axis B = " << d.inner_core_axis.B.ToDouble() << "\n";
    std::cout << "annular_axis B = " << d.annular_axis.B.ToDouble() << "\n";
    std::cout << "num complement_axes = " << d.complement_axes.size() << "\n";
    std::cout << "lam = " << d.lam.ToDouble() << "\n";
    std::cout << "w = [" << d.w[0].ToDouble() << ", " << d.w[1].ToDouble() << ", " << d.w[2].ToDouble() << "]\n";
  }
  return 0;
}
