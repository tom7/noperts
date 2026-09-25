#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  if (!root) return 1;

  TreeNode *found = nullptr;
  auto dfs = [&](auto &self, TreeNode *node) -> void {
    if (found) return;
    if (node->direct_cert.has_value()) {
      found = node;
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  dfs(dfs, root.get());

  if (!found) {
    std::cout << "no cert found\n";
    return 1;
  }

  std::cout << "Found path: " << found->path << "\n";
  const TubeCertificate &cert = *found->direct_cert;
  TriangleQ tri = found->GetTriangle();

  for (int a = 0; a < 4; a++) {
    ContactInfo ct[3] = {cert.axes[a].contacts[0], cert.axes[a].contacts[1], cert.axes[a].contacts[2]};
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    Tube229::AuditAxis(tri, ct, &ax, &center, &delta, &err);
    std::cout << "Axis " << a << ":\n";
    std::cout << "  center = (" << center.x.ToDouble() << ", " << center.y.ToDouble() << ", " << center.z.ToDouble() << ")\n";
    std::cout << "  B = " << ax.B.ToDouble() << ", delta = " << delta.ToDouble() << "\n";
  }

  return 0;
}
