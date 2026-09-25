#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static inline double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  TreeNode *target = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (node->path == target_path) { target = node; return; }
    for (auto &c : node->children) self(self, c.get());
  };
  find(find, root.get());
  if (!target || !target->decomposed_cert) return 1;

  const auto &dec = *target->decomposed_cert;
  for (int a = 0; a < 3; a++) {
    ContactInfo ct[3] = {dec.complement_axes[a].contacts[0], dec.complement_axes[a].contacts[1], dec.complement_axes[a].contacts[2]};
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    bool ok = Tube229::AuditAxis(tri, ct, &ax, &center, &delta, &err, BigRat(0));
    std::cout << "Comp axis " << a << " audit on tri: " << (ok ? "OK" : ("FAIL: " + err)) << "\n";
    std::cout << "  center = (" << center.x.ToDouble() << ", " << center.y.ToDouble() << ", " << center.z.ToDouble() << ")\n";
    std::cout << "  B = " << ax.B.ToDouble() << ", delta = " << delta.ToDouble() << "\n";
  }

  return 0;
}
