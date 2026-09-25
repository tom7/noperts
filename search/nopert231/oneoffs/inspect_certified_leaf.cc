#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::unique_ptr<TubeTreeNode> root = LoadTubeTreePack("local-view0.pack");
  if (!root) {
    std::cout << "Failed to load local-view0.pack\n";
    return 1;
  }

  // Find first leaf with direct_cert
  const TubeTreeNode *found = nullptr;
  auto dfs = [&](auto &self, const TubeTreeNode *n) -> void {
    if (found) return;
    if (n->direct_cert.has_value()) {
      found = n;
      return;
    }
    for (const auto &c : n->children) self(self, c.get());
  };
  dfs(dfs, root.get());

  if (!found) {
    std::cout << "No direct_cert found\n";
    return 1;
  }

  std::cout << "Found certified node at path: " << found->path << "\n";
  const TubeCertificate &cert = found->direct_cert.value();
  std::cout << "r = " << cert.r.ToString() << " (" << cert.r.ToDouble() << ")\n";
  std::cout << "c = " << cert.c.ToString() << " (" << cert.c.ToDouble() << ")\n";
  std::cout << "delta = " << cert.delta.ToString() << " (" << cert.delta.ToDouble() << ")\n";

  TriangleQ tri = found->GetTriangle();
  BigVecQ3 centers[4];
  BigRat deltas[4];
  for (int a = 0; a < 4; a++) {
    ContactInfo ct[3] = {cert.axes[a].contacts[0], cert.axes[a].contacts[1], cert.axes[a].contacts[2]};
    AxisCertificate ax;
    std::string err;
    Tube229::AuditAxis(tri, ct, &ax, &centers[a], &deltas[a], &err);
    std::cout << "Axis " << a << " center = ("
              << centers[a].x.ToDouble() << ", "
              << centers[a].y.ToDouble() << ", "
              << centers[a].z.ToDouble() << "), B=" << ax.B.ToDouble() << "\n";
  }

  return 0;
}
