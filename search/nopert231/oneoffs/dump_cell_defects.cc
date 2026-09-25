#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

void PrintBigRat(const BigRat &q) {
  std::cout << q.Numerator().ToString() << " / " << q.Denominator().ToString();
}

int main() {
  std::string p = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(p);

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

  BigRat defect[4][3];
  BigRat D[4];

  for (int j = 0; j < 4; j++) {
    for (int i = 0; i < 3; i++) {
      defect[j][i] = 0;
      const auto &c = cert.axes[j].contacts[i];
      // compute max error over all 20 vertices and 3 corners
      BigVecQ3 edge = Tube229::GetEdgeQ(c);
      for (int k = 0; k < 20; k++) {
        BigVecQ3 delta = Tube229::VertexQ(k) - Tube229::VertexQ(c.vertex);
        BigVecQ3 cross = yocto::cross(edge, delta);
        for (int cn = 0; cn < 3; cn++) {
          BigRat dot = yocto::dot(tri.corners[cn], cross);
          if (dot > defect[j][i]) defect[j][i] = dot;
        }
      }
    }
    // D[j] = sum_i (upper_weight[j][i] * defect[j][i])
    // upper_weight is bounded by 2
    D[j] = (defect[j][0] + defect[j][1] + defect[j][2]) * BigRat(2, 1);
  }

  std::cout << "def defect : Fin 4 → Fin 3 → ℚ := ![\n";
  for (int j = 0; j < 4; j++) {
    std::cout << "  ![";
    PrintBigRat(defect[j][0]); std::cout << ", ";
    PrintBigRat(defect[j][1]); std::cout << ", ";
    PrintBigRat(defect[j][2]); std::cout << "]" << (j < 3 ? "," : "") << "\n";
  }
  std::cout << "]\n\n";

  std::cout << "def D : Fin 4 → ℚ := ![";
  for (int j = 0; j < 4; j++) {
    PrintBigRat(D[j]);
    if (j < 3) std::cout << ", ";
  }
  std::cout << "]\n";

  return 0;
}
