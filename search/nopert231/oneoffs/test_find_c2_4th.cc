#include <iostream>
#include <iomanip>
#include <vector>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  BigVecQ3 c2 = tri1.corners[2];
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

  auto root = LoadTreeJson("ruperts/.artifacts/nopert229/tree_0.json", false, "ruperts/.artifacts/nopert229");
  std::string p0 = "031213002112122012120";
  TreeNode *n0 = nullptr;
  auto find_node = [&](auto &self, TreeNode *n) -> void {
    if (!n || n0) return;
    if (n->path == p0) { n0 = n; return; }
    if (p0.starts_with(n->path)) {
      for (auto &c : n->children) self(self, c.get());
    }
  };
  find_node(find_node, root.get());
  const auto &sib_cert = *n0->direct_cert;

  Tube229::CandidateTriple cand1, cand2, cand3;
  Tube229::DoubleCheckAxis(tri_c2, sib_cert.axes[1].contacts, &cand1, 1e-12);
  Tube229::DoubleCheckAxis(tri_c2, sib_cert.axes[2].contacts, &cand2, 1e-12);
  Tube229::DoubleCheckAxis(tri_c2, sib_cert.axes[3].contacts, &cand3, 1e-12);

  vec3 p1 = cand1.normalized_a;
  vec3 p2 = cand2.normalized_a;
  vec3 p3 = cand3.normalized_a;

  // We need p0 such that 0 is in conv(p0, p1, p2, p3) with strict positive weights!
  // Face (1,2,3) has normal:
  vec3 n = yocto::cross(p2 - p1, p3 - p1);
  n = yocto::normalize(n);
  double d = yocto::dot(n, p1);
  std::cout << "Normal to face (1,2,3): (" << n.x << ", " << n.y << ", " << n.z << "), d = " << d << "\n";
  // The origin is at distance 0 from origin, so dot(n, 0) - d = -d.
  // We need dot(n, p0) to have OPPOSITE sign of d!
  std::cout << "Target sign for dot(n, p0) - d: " << (-d > 0 ? "POSITIVE" : "NEGATIVE") << "\n";
  std::cout << "Specifically, dot(n, p0) must be " << (d < 0 ? "> " : "< ") << d << "\n";

  return 0;
}
