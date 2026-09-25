#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

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
  bool ok = Tube229::AuditAxis(target->GetTriangle(), c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000000"));
  std::cout << "AuditAxis on c_ann with defect tol: " << (ok ? "OK" : ("FAIL: " + err)) << "\n";
  std::cout << "p0 = (" << ctr_ann.x.ToDouble() << ", " << ctr_ann.y.ToDouble() << ", " << ctr_ann.z.ToDouble() << ")\n";
  std::cout << "B = " << ax_ann.B.ToDouble() << "\n";

  return 0;
}
