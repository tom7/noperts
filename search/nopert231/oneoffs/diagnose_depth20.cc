#include <iostream>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  TreeNode *target_leaf = nullptr;
  auto find_leaf = [&](auto &self, TreeNode *node) -> void {
    if (!node || target_leaf) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) return;
    if (node->depth() == 21 && node->children.empty() && !node->external) {
      target_leaf = node;
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  find_leaf(find_leaf, root.get());

  if (!target_leaf) {
    std::cout << "No uncertified leaf found at depth 20\n";
    return 1;
  }

  std::cout << "Target leaf: " << target_leaf->path << " (depth " << target_leaf->depth() << ")\n";
  TriangleQ tri = target_leaf->GetTriangle();

  TubeCertificate cert;
  std::cout << "\n1. Testing fast_pass...\n" << std::flush;
  bool f_ok = Tube229::SynthesizeCertificate(tri, 20, &cert, {}, {}, /*fast_only=*/true);
  std::cout << "Fast pass: " << (f_ok ? "SUCCESS" : "FAIL") << "\n" << std::flush;

  std::cout << "\n2. Testing multi-view cutting-plane pass...\n" << std::flush;
  bool m_ok = Tube229::SynthesizeCertificate(tri, 20, &cert, {}, {}, /*fast_only=*/false);
  std::cout << "Multi-view pass: " << (m_ok ? "SUCCESS" : "FAIL") << "\n" << std::flush;
  if (m_ok) {
    std::cout << "  c = " << cert.c.ToString() << " (" << cert.c.ToDouble() << ")\n";
    std::cout << "  r = " << cert.r.ToString() << " (" << cert.r.ToDouble() << ")\n";
  }

  // 3. Find siblings
  std::string parent_path = target_leaf->path.substr(0, target_leaf->path.size() - 1);
  std::cout << "\nParent path: " << parent_path << "\n";
  TreeNode *parent = nullptr;
  auto find_parent = [&](auto &self, TreeNode *node) -> void {
    if (!node || parent) return;
    if (node->path == parent_path) {
      parent = node;
      return;
    }
    if (parent_path.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find_parent(find_parent, root.get());

  if (parent) {
    std::cout << "Found parent! Children count: " << parent->children.size() << "\n";
    for (size_t ci = 0; ci < parent->children.size(); ci++) {
      auto &child = parent->children[ci];
      std::cout << "  Child " << ci << " (" << child->path << "): ";
      if (child->direct_cert.has_value() && BigRat::Sign(child->direct_cert->r) > 0) {
        std::cout << "CERTIFIED! r=" << child->direct_cert->r.ToDouble()
                  << " c=" << child->direct_cert->c.ToDouble() << "\n";
        // Test auditing sibling cert on target_leaf!
        TubeCertificate out_c;
        std::string fail_msg;
        bool sib_audit = Tube229::AuditCertificateAdaptive(tri, *child->direct_cert, &out_c, &fail_msg);
        std::cout << "    Direct sibling audit on target: " << (sib_audit ? "SUCCESS!" : ("FAIL: " + fail_msg)) << "\n";
        if (sib_audit) {
          std::cout << "      r=" << out_c.r.ToDouble() << " c=" << out_c.c.ToDouble() << "\n";
        }
      } else {
        std::cout << "UNCERTIFIED (" << (child->children.empty() ? "leaf" : "internal") << ")\n";
      }
    }
  }

  return 0;
}
