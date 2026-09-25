#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static void PrintAxis(const std::string &name, const AxisCertificate &ax) {
  std::cout << "  let " << name << " : AxisCertificate := {\n";
  std::cout << "    edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "],\n";
  std::cout << "    edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "],\n";
  std::cout << "    edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "],\n";
  std::cout << "    edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "],\n";
  std::cout << "    mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "],\n";
  std::cout << "    index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "],\n";
  std::cout << "    nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "],\n";
  std::cout << "    B := " << ax.B.Numerator().ToString() << " / " << ax.B.Denominator().ToString() << "\n";
  std::cout << "  }\n";
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
  bool audit_ok = Tube229::AuditAxis(target->GetTriangle(), c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));
  std::cout << "Audit ax_ann ok: " << audit_ok << ", del_ann = " << del_ann.ToString() << ", err = " << err << "\n";
  PrintAxis("ax0", ax_ann);

  for (size_t a = 0; a < dec.complement_axes.size(); a++) {
    PrintAxis("ax" + std::to_string(a + 1), dec.complement_axes[a]);
  }

  PrintAxis("coreAx", dec.inner_core_axis);

  std::cout << "  defect0: " << dec.defect0[0].ToString() << ", " << dec.defect0[1].ToString() << ", " << dec.defect0[2].ToString() << "\n";
  std::cout << "  defect_D: " << dec.defect_D.ToString() << "\n";
  std::cout << "  c_cone: " << dec.c_cone.ToString() << "\n";
  std::cout << "  c_core: " << dec.c_core.ToString() << "\n";
  std::cout << "  r_min: " << dec.r_min.ToString() << "\n";
  std::cout << "  r: " << dec.r.ToString() << "\n";
  std::cout << "  delta: " << dec.delta.ToString() << "\n";
  std::cout << "  c_comp: " << dec.c_comp.ToString() << "\n";
  std::cout << "  lam: " << dec.lam.ToString() << "\n";
  std::cout << "  w: " << dec.w[0].ToString() << ", " << dec.w[1].ToString() << ", " << dec.w[2].ToString() << "\n";

  return 0;
}
