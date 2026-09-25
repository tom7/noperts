#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  TreeNode *target = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (node->path == "03121300") { target = node; return; }
    for (auto &c : node->children) self(self, c.get());
  };
  find(find, root.get());
  if (!target) {
    std::cout << "Target node 03121300 not found!\n";
    return 1;
  }
  if (!target->decomposed_cert.has_value()) {
    std::cout << "Target node 03121300 has no decomposed cert!\n";
    return 1;
  }
  const auto &dec = *target->decomposed_cert;

  ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(target->GetTriangle(), c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));

  ContactInfo c_core[3];
  for (int m = 0; m < 3; m++) {
    c_core[m] = dec.inner_core_axis.contacts[m];
    std::swap(c_core[m].edge_start, c_core[m].edge_finish);
    std::swap(c_core[m].edge_start2, c_core[m].edge_finish2);
    c_core[m].mix = 1000 - c_core[m].mix;
  }
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  bool core_ok = Tube229::AuditAxis(target->GetTriangle(), c_core, &ax_core, &ctr_core, &del_core, &err, BigRat("1/1000"));
  std::cout << "core_ok: " << core_ok << ", err: " << err << "\n";

  BigVecQ3 u0 = ctr_ann / ax_ann.B;
  BigVecQ3 u_core = ctr_core / ax_core.B;

  BigRat dot = BigVecQ3::Dot(u_core, u0);
  BigRat norm_sq0 = BigVecQ3::Dot(u0, u0);
  BigRat lam = dot / norm_sq0;
  BigVecQ3 w = u_core - u0 * lam;
  BigRat norm_sq_w = BigVecQ3::Dot(w, w);

  std::cout << "ax_core witness: " << ax_core.nonzero_witness[0] << ", " << ax_core.nonzero_witness[1] << ", " << ax_core.nonzero_witness[2] << "\n";
  std::cout << "u0: " << u0[0].ToDouble() << ", " << u0[1].ToDouble() << ", " << u0[2].ToDouble() << "\n";
  std::cout << "u_core: " << u_core[0].ToDouble() << ", " << u_core[1].ToDouble() << ", " << u_core[2].ToDouble() << "\n";
  std::cout << "lam: " << lam.ToDouble() << "\n";
  std::cout << "||w||: " << std::sqrt(norm_sq_w.ToDouble()) << "\n";
  std::cout << "||w||^2: " << norm_sq_w.ToString() << "\n";

  return 0;
}
