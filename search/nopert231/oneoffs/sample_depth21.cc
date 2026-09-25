#include <iostream>
#include <vector>
#include <unordered_map>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(file, false, "ruperts/.artifacts/nopert229");
  if (!root) return 1;

  // Build a lookup map of all certified nodes in the tree
  std::unordered_map<std::string, const TubeCertificate*> cert_map;
  std::vector<TreeNode*> depth21_leaves;

  auto index_tree = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) {
      cert_map[node->path] = &*node->direct_cert;
    }
    if (node->depth() == 21 && node->children.empty() && !node->external &&
        (!node->direct_cert.has_value() || BigRat::Sign(node->direct_cert->r) <= 0)) {
      depth21_leaves.push_back(node);
    }
    for (auto &c : node->children) self(self, c.get());
  };
  index_tree(index_tree, root.get());

  std::cout << "Indexed " << cert_map.size() << " certified nodes in tree.\n";
  std::cout << "Found " << depth21_leaves.size() << " uncertified depth-21 leaves.\n";

  // Test sibling certificates on a sample of 200 depth-21 leaves
  int sample_count = std::min((int)depth21_leaves.size(), 200);
  int stride = depth21_leaves.size() / sample_count;

  int direct_sib_success = 0;
  int has_certified_sibling = 0;
  int has_certified_cousin = 0;

  for (int i = 0; i < sample_count; i++) {
    TreeNode *leaf = depth21_leaves[i * stride];
    TriangleQ tri = leaf->GetTriangle();

    // Check 3 siblings: parent + '0', '1', '2', '3'
    std::string parent_path = leaf->path.substr(0, leaf->path.size() - 1);
    bool found_sib = false;
    bool direct_ok = false;

    for (char c : {'0', '1', '2', '3'}) {
      std::string sib_path = parent_path + c;
      if (sib_path == leaf->path) continue;
      auto it = cert_map.find(sib_path);
      if (it != cert_map.end()) {
        found_sib = true;
        TubeCertificate out_c;
        std::string fail_msg;
        if (Tube229::AuditCertificateAdaptive(tri, *it->second, &out_c, &fail_msg)) {
          if (BigRat::Sign(out_c.r) > 0 && BigRat::Sign(out_c.c) > 0) {
            direct_ok = true;
            break;
          }
        }
      }
    }
    if (found_sib) has_certified_sibling++;
    if (direct_ok) direct_sib_success++;

    // If no sibling, check cousins (grandparent + ...)
    if (!found_sib && parent_path.size() >= 2) {
      std::string gp_path = parent_path.substr(0, parent_path.size() - 1);
      for (char c1 : {'0', '1', '2', '3'}) {
        for (char c2 : {'0', '1', '2', '3'}) {
          std::string cousin_path = gp_path + c1 + c2;
          if (cousin_path == leaf->path) continue;
          if (cert_map.count(cousin_path)) {
            has_certified_cousin++;
            goto next_sample;
          }
        }
      }
    }
  next_sample:;
  }

  std::cout << "\nResults across " << sample_count << " sampled depth-21 leaves:\n"
            << "  Has certified sibling: " << has_certified_sibling << " (" << (has_certified_sibling * 100.0 / sample_count) << "%)\n"
            << "  Direct sibling audit SUCCESS: " << direct_sib_success << " (" << (direct_sib_success * 100.0 / sample_count) << "%)\n"
            << "  Has certified cousin (if no sibling): " << has_certified_cousin << "\n";

  return 0;
}
