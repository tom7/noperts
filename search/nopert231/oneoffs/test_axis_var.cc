#include <iostream>
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
  const auto &dec = *target->decomposed_cert;

  ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(target->GetTriangle(), c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));

  std::cout << "Annular axis: delta_req = " << del_ann.ToDouble() << ", B = " << ax_ann.B.ToDouble() << "\n";

  for (int a = 0; a < 3; a++) {
    ContactInfo ct[3] = {dec.complement_axes[a].contacts[0], dec.complement_axes[a].contacts[1], dec.complement_axes[a].contacts[2]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    Tube229::AuditAxis(target->GetTriangle(), ct, &ax, &ctr, &del, &err, BigRat(0));
    std::cout << "Comp axis " << a << ": delta_req = " << del.ToDouble() << ", B = " << ax.B.ToDouble() << "\n";
  }

  return 0;
}
