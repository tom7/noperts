#include <iostream>
#include <vector>
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  std::string target_path = "031213";
  TreeNode *target_node = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == target_path) { target_node = node; return; }
    if (target_path.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find(find, root.get());

  if (!target_node) {
    std::cout << "Node 031213 not found!\n";
    return 1;
  }

  std::cout << "Node 031213 found!\n";
  std::cout << "  Depth: " << target_node->depth() << "\n";
  std::cout << "  Children: " << target_node->children.size() << "\n";
  std::cout << "  Certified: " << (target_node->direct_cert.has_value() ? "YES" : "NO") << "\n";

  TriangleQ tri = target_node->GetTriangle();
  std::cout << "  Corner 0: (" << tri.corners[0].x.ToDouble() << ", " << tri.corners[0].y.ToDouble() << ", " << tri.corners[0].z.ToDouble() << ")\n";
  std::cout << "  Corner 1: (" << tri.corners[1].x.ToDouble() << ", " << tri.corners[1].y.ToDouble() << ", " << tri.corners[1].z.ToDouble() << ")\n";
  std::cout << "  Corner 2: (" << tri.corners[2].x.ToDouble() << ", " << tri.corners[2].y.ToDouble() << ", " << tri.corners[2].z.ToDouble() << ")\n";

  // Check its parent 03121
  TreeNode *parent = nullptr;
  std::string p_path = "03121";
  auto find_p = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p_path) { parent = node; return; }
    if (p_path.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find_p(find_p, root.get());

  if (parent) {
    std::cout << "Parent 03121 found! Children: " << parent->children.size() << "\n";
    for (size_t i = 0; i < parent->children.size(); i++) {
      auto &c = parent->children[i];
      std::cout << "  Child " << i << " (" << c->path << "): "
                << (c->direct_cert.has_value() ? "CERTIFIED" : "UNCERTIFIED")
                << " children=" << c->children.size() << "\n";
    }
  }

  return 0;
}
