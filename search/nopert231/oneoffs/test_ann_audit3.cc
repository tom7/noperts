#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static inline double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  TreeNode *target = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (node->path == "03121300") { target = node; return; }
    for (auto &c : node->children) self(self, c.get());
  };
  find(find, root.get());
  const auto &dec = *target->decomposed_cert;

  ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  bool ok = Tube229::AuditAxis(target->GetTriangle(), c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));
  std::cout << "AuditAxis on c_ann with defect tol: " << (ok ? "OK" : ("FAIL: " + err)) << "\n";
  std::cout << "p0 = (" << ctr_ann.x.ToDouble() << ", " << ctr_ann.y.ToDouble() << ", " << ctr_ann.z.ToDouble() << ")\n";

  ContactInfo ct0[3] = {dec.complement_axes[0].contacts[0], dec.complement_axes[0].contacts[1], dec.complement_axes[0].contacts[2]};
  ContactInfo ct1[3] = {dec.complement_axes[1].contacts[0], dec.complement_axes[1].contacts[1], dec.complement_axes[1].contacts[2]};
  ContactInfo ct2[3] = {dec.complement_axes[2].contacts[0], dec.complement_axes[2].contacts[1], dec.complement_axes[2].contacts[2]};

  BigVecQ3 ctr0, ctr1, ctr2;
  AxisCertificate ax0, ax1, ax2;
  BigRat del0, del1, del2;
  Tube229::AuditAxis(target->GetTriangle(), ct0, &ax0, &ctr0, &del0, &err, BigRat(0));
  Tube229::AuditAxis(target->GetTriangle(), ct1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(target->GetTriangle(), ct2, &ax2, &ctr2, &del2, &err, BigRat(0));

  vec3 p0 = {ctr_ann.x.ToDouble(), ctr_ann.y.ToDouble(), ctr_ann.z.ToDouble()};
  vec3 p1 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  vec3 p2 = {ctr1.x.ToDouble(), ctr1.y.ToDouble(), ctr1.z.ToDouble()};
  vec3 p3 = {ctr2.x.ToDouble(), ctr2.y.ToDouble(), ctr2.z.ToDouble()};

  vec3 d0 = p0 - p3;
  vec3 d1 = p1 - p3;
  vec3 d2 = p2 - p3;
  double d = Det3(d0, d1, d2);
  std::cout << "Det3 = " << d << "\n";

  vec3 dp = -p3; // origin
  double b0 = Det3(dp, d1, d2) / d;
  double b1 = Det3(d0, dp, d2) / d;
  double b2 = Det3(d0, d1, dp) / d;
  double b3 = 1.0 - b0 - b1 - b2;
  std::cout << "Origin barycentric coords: b0=" << b0 << ", b1=" << b1 << ", b2=" << b2 << ", b3=" << b3 << "\n";

  return 0;
}
