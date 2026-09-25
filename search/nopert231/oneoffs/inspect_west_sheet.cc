#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::cout << "Loading tree...\n";
  auto root = LoadTreeJson(".artifacts/nopert229/tree_0.json");
  if (!root) {
    std::cout << "Failed to load tree\n";
    return 1;
  }

  // Find the first uncertified leaf under 03121303
  std::string target_leaf;
  auto find_uncert = [&](auto &self, const TreeNode &node, const std::string &path) -> bool {
    if (path.size() >= 8 && path.substr(0, 8) != "03121303") return false;
    if (node.children.empty()) {
      if (!node.direct_cert.has_value() && !node.decomposed_cert.has_value()) {
        target_leaf = path;
        return true;
      }
      return false;
    }
    for (size_t i = 0; i < node.children.size(); i++) {
      if (node.children[i]) {
        if (self(self, *node.children[i], path + std::to_string(i))) return true;
      }
    }
    return false;
  };

  find_uncert(find_uncert, *root, "0");
  std::cout << "Found sample uncertified leaf in West sheet: " << target_leaf
            << " (len " << target_leaf.size() << ")\n";

  if (target_leaf.empty()) return 0;

  // Find nearest certified node to target_leaf
  TriangleQ leaf_tri = TriangleFromPath(target_leaf);
  vec3 c0 = {leaf_tri.corners[0].x.ToDouble(), leaf_tri.corners[0].y.ToDouble(), leaf_tri.corners[0].z.ToDouble()};
  vec3 c1 = {leaf_tri.corners[1].x.ToDouble(), leaf_tri.corners[1].y.ToDouble(), leaf_tri.corners[1].z.ToDouble()};
  vec3 c2 = {leaf_tri.corners[2].x.ToDouble(), leaf_tri.corners[2].y.ToDouble(), leaf_tri.corners[2].z.ToDouble()};
  vec3 center = yocto::normalize(c0 + c1 + c2);

  auto nearest = FindNearestCertifiedNode(*root, center);
  const TubeCertificate *sib = nullptr;
  if (nearest.has_value()) {
    std::cout << "Nearest certified node: " << nearest->path << " (r=" << nearest->direct_r_rat.ToString() << ")\n";
    const TreeNode *curr = root.get();
    for (size_t i = 1; i < nearest->path.size(); i++) {
      int idx = nearest->path[i] - '0';
      if (idx >= 0 && idx < (int)curr->children.size()) curr = curr->children[idx].get();
      else { curr = nullptr; break; }
    }
    if (curr && curr->direct_cert.has_value()) sib = &curr->direct_cert.value();
  }

  // Also test with base_sib from depth 21
  ContactInfo cont0[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  ContactInfo cont1[3] = {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}};
  ContactInfo cont2[3] = {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}};
  ContactInfo cont3[3] = {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}};

  TubeCertificate base_sib;
  for (int m = 0; m < 3; m++) {
    base_sib.axes[0].contacts[m] = cont0[m];
    base_sib.axes[1].contacts[m] = cont1[m];
    base_sib.axes[2].contacts[m] = cont2[m];
    base_sib.axes[3].contacts[m] = cont3[m];
  }
  base_sib.axes[0].B = BigRat(139673967, 100000000);
  base_sib.axes[1].B = BigRat(176, 100);
  base_sib.axes[2].B = BigRat(176, 100);
  base_sib.axes[3].B = BigRat(176, 100);
  base_sib.delta = BigRat(333, 1000000000);
  base_sib.symmetry_index = 0;

  std::cout << "\n=== Testing ancestors of target leaf in West sheet ===\n";
  for (int len = target_leaf.size(); len >= 8; len--) {
    std::string p = target_leaf.substr(0, len);
    TriangleQ tri = TriangleFromPath(p);

    DecomposedCertificate dc;
    std::string fail;
    bool ok = Tube229::SynthesizeDecomposedCertificate(tri, len, &dc, sib ? sib : &base_sib, &fail);
    std::cout << "Depth " << len << " (" << p << "): "
              << (ok ? "SUCCESS!" : ("FAIL: " + fail)) << "\n";
    if (ok) {
      std::cout << "  r_min=" << dc.r_min.ToString() << " r=" << dc.r.ToString()
                << " c_cone=" << dc.c_cone.ToString() << " c_comp=" << dc.c_comp.ToString()
                << " delta=" << dc.delta.ToString() << "\n";
    }
  }

  return 0;
}
