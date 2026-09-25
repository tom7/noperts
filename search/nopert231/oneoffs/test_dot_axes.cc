#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

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
  const auto &cert = *n0->direct_cert;

  vec3 uncov = {0.401011, -0.483067, -0.778355};
  uncov = yocto::normalize(uncov);

  std::cout << std::setprecision(10);
  for (int a = 0; a < 4; a++) {
    Tube229::CandidateTriple cand;
    Tube229::DoubleCheckAxis(tri1, cert.axes[a].contacts, &cand, 1e-8);
    std::cout << "Axis " << a << ": norm_a = ("
              << cand.normalized_a.x << ", " << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
    std::cout << "  dot(norm_a, uncov) = " << yocto::dot(cand.normalized_a, uncov) << "\n";
  }

  return 0;
}
