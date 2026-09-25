#include <iostream>
#include <iomanip>
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

  ContactInfo repl0[3] = {
    {19, 3, 19, 3, 0, 19},
    {4, 8, 4, 8, 0, 4},
    {10, 15, 10, 15, 0, 10}
  };

  Tube229::CandidateTriple cand0, cand1, cand2, cand3;
  bool ok0 = Tube229::DoubleCheckAxis(tri_c2, repl0, &cand0, 1e-12);
  bool ok1 = Tube229::DoubleCheckAxis(tri_c2, sib_cert.axes[1].contacts, &cand1, 1e-12);
  bool ok2 = Tube229::DoubleCheckAxis(tri_c2, sib_cert.axes[2].contacts, &cand2, 1e-12);
  bool ok3 = Tube229::DoubleCheckAxis(tri_c2, sib_cert.axes[3].contacts, &cand3, 1e-12);

  std::cout << "ok0=" << ok0 << " ok1=" << ok1 << " ok2=" << ok2 << " ok3=" << ok3 << "\n";

  vec3 p0_v = cand0.normalized_a;
  vec3 p1_v = cand1.normalized_a;
  vec3 p2_v = cand2.normalized_a;
  vec3 p3_v = cand3.normalized_a;

  std::cout << "p0 = (" << p0_v.x << ", " << p0_v.y << ", " << p0_v.z << ")\n";
  std::cout << "p1 = (" << p1_v.x << ", " << p1_v.y << ", " << p1_v.z << ")\n";
  std::cout << "p2 = (" << p2_v.x << ", " << p2_v.y << ", " << p2_v.z << ")\n";
  std::cout << "p3 = (" << p3_v.x << ", " << p3_v.y << ", " << p3_v.z << ")\n";

  vec3 a = p0_v - p3_v;
  vec3 b = p1_v - p3_v;
  vec3 c = p2_v - p3_v;
  double det = yocto::dot(a, yocto::cross(b, c));
  vec3 rhs = -p3_v;
  double w0 = yocto::dot(rhs, yocto::cross(b, c)) / det;
  double w1 = yocto::dot(a, yocto::cross(rhs, c)) / det;
  double w2 = yocto::dot(a, yocto::cross(b, rhs)) / det;
  double w3 = 1.0 - w0 - w1 - w2;

  std::cout << "det = " << det << "\n";
  std::cout << "Barycentric weights of 0:\n"
            << "  w0 = " << w0 << "\n"
            << "  w1 = " << w1 << "\n"
            << "  w2 = " << w2 << "\n"
            << "  w3 = " << w3 << "\n";

  return 0;
}
