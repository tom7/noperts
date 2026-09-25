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
  const auto &sib_cert = *n0->direct_cert;

  Tube229::CandidateTriple cand2;
  bool ok2 = Tube229::DoubleCheckAxis(tri1, sib_cert.axes[2].contacts, &cand2, 0.0);
  std::cout << "Axis 2 strict check on tri1: " << (ok2 ? "PASS" : "FAIL") << "\n";
  std::cout << std::setprecision(12);
  std::cout << "  strict_slack = " << cand2.strict_slack << "\n";
  std::cout << "  B = " << cand2.B << "\n";
  std::cout << "  norm_a = (" << cand2.normalized_a.x << ", "
            << cand2.normalized_a.y << ", " << cand2.normalized_a.z << ")\n";

  vec3 uncov = yocto::normalize(vec3{0.401011, -0.483067, -0.778355});
  std::cout << "  dot(norm_a, uncov) = " << yocto::dot(cand2.normalized_a, uncov) << "\n";

  return 0;
}
