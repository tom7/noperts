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

  ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err);

  BigVecQ3 comp_centers[3];
  AxisCertificate comp_axes[3];
  BigRat comp_deltas[3];
  for (int a = 0; a < 3; a++) {
    ContactInfo ct[3] = {dec.complement_axes[a].contacts[0], dec.complement_axes[a].contacts[1], dec.complement_axes[a].contacts[2]};
    Tube229::AuditAxis(tri, ct, &comp_axes[a], &comp_centers[a], &comp_deltas[a], &err);
  }

  vec3 p0 = {ctr_ann.x.ToDouble(), ctr_ann.y.ToDouble(), ctr_ann.z.ToDouble()};
  vec3 p1 = {comp_centers[0].x.ToDouble(), comp_centers[0].y.ToDouble(), comp_centers[0].z.ToDouble()};
  vec3 p2 = {comp_centers[1].x.ToDouble(), comp_centers[1].y.ToDouble(), comp_centers[1].z.ToDouble()};
  vec3 p3 = {comp_centers[2].x.ToDouble(), comp_centers[2].y.ToDouble(), comp_centers[2].z.ToDouble()};

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
  std::cout << "Original tree_0_complete.json barycentric coords: b0=" << b0 << ", b1=" << b1 << ", b2=" << b2 << ", b3=" << b3 << "\n";

  return 0;
}
