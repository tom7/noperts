#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  if (!root) return 1;

  std::string p0 = "031213002112122012120";
  TreeNode *n0 = nullptr;
  auto find_nodes = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->path == p0) n0 = node;
    if (n0) return;
    if (p0.starts_with(node->path)) {
      for (auto &c : node->children) self(self, c.get());
    }
  };
  find_nodes(find_nodes, root.get());

  if (!n0 || !n0->direct_cert.has_value()) {
    std::cout << "n0 not found or no cert\n";
    return 1;
  }

  std::cout << "Found n0 certified leaf!\n";
  const TubeCertificate &cert = *n0->direct_cert;
  TriangleQ tri = n0->GetTriangle();

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
    for (int c = 0; c < 3; c++) {
      std::cout << "  Contact " << c << ": (" << ct[c].edge_start << "->" << ct[c].edge_finish << ", "
                << ct[c].edge_start2 << "->" << ct[c].edge_finish2 << ", mix=" << ct[c].mix << ", v=" << ct[c].vertex << ")\n";
    }
  }

  return 0;
}
