#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

static std::string LeanContact(const ContactInfo &c, int field) {
  // returns edgeStart, edgeFinish, edgeStart2, edgeFinish2, mix, index
  if (field == 0) return std::to_string(c.edge_start);
  if (field == 1) return std::to_string(c.edge_finish);
  if (field == 2) return std::to_string(c.edge_start2);
  if (field == 3) return std::to_string(c.edge_finish2);
  if (field == 4) return std::to_string(c.mix);
  if (field == 5) return std::to_string(c.vertex);
  return "";
}

static void PrintLeanAxis(const std::string &name, const AxisCertificate &ax) {
  std::cout << "  let " << name << " : AxisCertificate := {\n";
  std::cout << "    edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "],\n";
  std::cout << "    edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "],\n";
  std::cout << "    edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "],\n";
  std::cout << "    edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "],\n";
  std::cout << "    mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "],\n";
  std::cout << "    index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "],\n";
  std::cout << "    nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "],\n";
  std::cout << "    B := " << ax.B.ToString() << "\n";
  std::cout << "  }\n";
}

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");

  std::string target_path = "03121303200";
  TreeNode *node = nullptr;
  auto find = [&](auto &self, TreeNode *n) -> void {
    if (n->path == target_path) { node = n; return; }
    for (auto &c : n->children) self(self, c.get());
  };
  find(find, root.get());

  if (!node || !node->decomposed_cert) {
    std::cerr << "Node not found or no decomposed cert!\n";
    return 1;
  }

  TriangleQ tri = TriangleFromPath(target_path);

  // Annular axis:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));

  // Core axis:
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

  // Complement axes:
  const auto &dc = *node->decomposed_cert;
  AxisCertificate ax_comp[3];
  BigVecQ3 ctr_comp[3];
  BigRat del_comp[3];
  for (int i = 0; i < 3; i++) {
    ContactInfo c[3] = {dc.complement_axes[i].contacts[0], dc.complement_axes[i].contacts[1], dc.complement_axes[i].contacts[2]};
    Tube229::AuditAxis(tri, c, &ax_comp[i], &ctr_comp[i], &del_comp[i], &err, BigRat(0));
  }

  // Calculate maximum delta across all 5 axes:
  BigRat max_delta = del_ann;
  if (BigRat::Greater(del_core, max_delta)) max_delta = del_core;
  for (int i = 0; i < 3; i++) {
    if (BigRat::Greater(del_comp[i], max_delta)) max_delta = del_comp[i];
  }

  // Defect calculation on annular axis:
  BigRat def0[3] = {BigRat(0), BigRat(0), BigRat(0)};
  for (int i = 0; i < 3; i++) def0[i] = dc.defect0[i];
  BigRat D0 = dc.defect_D;

  // Let us compute u0 and uc:
  BigVecQ3 u0 = {BigRat::Div(ctr_ann.x, ax_ann.B), BigRat::Div(ctr_ann.y, ax_ann.B), BigRat::Div(ctr_ann.z, ax_ann.B)};
  BigVecQ3 uc = {BigRat::Div(ctr_core.x, ax_core.B), BigRat::Div(ctr_core.y, ax_core.B), BigRat::Div(ctr_core.z, ax_core.B)};

  BigRat u0_sq = BigRat::Plus(BigRat::Plus(BigRat::Times(u0.x, u0.x), BigRat::Times(u0.y, u0.y)), BigRat::Times(u0.z, u0.z));
  BigRat dot_u0_uc = BigRat::Plus(BigRat::Plus(BigRat::Times(u0.x, uc.x), BigRat::Times(u0.y, uc.y)), BigRat::Times(u0.z, uc.z));
  BigRat lam = BigRat::Div(dot_u0_uc, u0_sq);
  BigVecQ3 w = {
    BigRat::Minus(uc.x, BigRat::Times(lam, u0.x)),
    BigRat::Minus(uc.y, BigRat::Times(lam, u0.y)),
    BigRat::Minus(uc.z, BigRat::Times(lam, u0.z))
  };

  std::cout << "import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree\n";
  std::cout << "import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate\n\n";
  std::cout << "open Noperthedron.Nopert229\n";
  std::cout << "open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree\n";
  std::cout << "open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate\n";
  std::cout << "open Noperthedron.SnubCube.ProjectiveView\n\n";
  std::cout << "def getTriangleForPath (digits : List (Fin 4)) : AtlasProjectiveView.Triangle ℚ :=\n";
  std::cout << "  digits.foldl (fun t d => split t d) AtlasProjectiveView.upperWedgeTriangle\n\n";
  std::cout << "def main : IO Unit := do\n";
  std::cout << "  let pathDigits : List (Fin 4) := [0, 3, 1, 2, 1, 3, 0, 3, 2, 0, 0]\n";
  std::cout << "  let tri := getTriangleForPath pathDigits\n\n";

  PrintLeanAxis("ax0", ax_ann);
  PrintLeanAxis("ax1", ax_comp[0]);
  PrintLeanAxis("ax2", ax_comp[1]);
  PrintLeanAxis("ax3", ax_comp[2]);
  PrintLeanAxis("coreAxis", ax_core);

  std::cout << "\n  let box : Box := {\n";
  std::cout << "    interval := AtlasPose.rootInterval ℚ,\n";
  std::cout << "    chart := 0, symmetryIndex := 0, root := 0,\n";
  std::cout << "    triangle := tri,\n";
  std::cout << "    certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,\n";
  std::cout << "    c := " << dc.c_comp.ToString() << ",\n";
  std::cout << "    δ := " << max_delta.ToString() << ",\n";
  std::cout << "    r := 1 / 500\n";
  std::cout << "  }\n\n";

  std::cout << "  let defect0 : Fin 3 → ℚ := fun | 0 => " << def0[0].ToString() << " | 1 => " << def0[1].ToString() << " | 2 => " << def0[2].ToString() << "\n";
  std::cout << "  let D0 : ℚ := " << D0.ToString() << "\n";
  std::cout << "  let r_min : ℚ := 1 / 500\n";
  std::cout << "  let c_cone : ℚ := 45 / 1000\n";
  std::cout << "  let c_core : ℚ := 5 / 1000\n";
  std::cout << "  let lam : ℚ := " << lam.ToString() << "\n";
  std::cout << "  let w : Fin 3 → ℚ := fun | 0 => " << w.x.ToString() << " | 1 => " << w.y.ToString() << " | 2 => " << w.z.ToString() << "\n\n";

  std::cout << "  let cbox := box.withCoreAxis coreAxis c_core r_min\n\n";

  std::cout << "  IO.println s!\"r_min_pos: {decide (0 < r_min)}\"\n";
  std::cout << "  IO.println s!\"r_pos: {decide (0 < box.r)}\"\n";
  std::cout << "  IO.println s!\"r_min_le_r: {decide (r_min ≤ box.r)}\"\n";
  std::cout << "  IO.println s!\"r_le_two: {decide (box.r ≤ 2)}\"\n";
  std::cout << "  IO.println s!\"delta_nonneg: {decide (0 ≤ box.δ)}\"\n";
  std::cout << "  IO.println s!\"c_nonneg: {decide (0 ≤ box.c)}\"\n";
  std::cout << "  IO.println s!\"bary: {decide (box.decomposedBarycentricValid c_cone)}\"\n";
  std::cout << "  IO.println s!\"D0_nonneg: {decide (0 ≤ D0)}\"\n";
  std::cout << "  IO.println s!\"defect0_nonneg: {decide (∀ i, 0 ≤ defect0 i)}\"\n";
  std::cout << "  IO.println s!\"defect_budget0: {decide ((∑ i, box.weightUpper 0 i * defect0 i) ≤ D0)}\"\n";
  std::cout << "  IO.println s!\"c_cone_margin: {decide (box.δ ≤ c_cone)}\"\n";
  std::cout << "  IO.println s!\"annular_dominance: {decide (((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤ r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))}\"\n";
  std::cout << "  IO.println s!\"B_pos: {decide (∀ j, 0 < (box.certificate j).B)}\"\n";
  std::cout << "  IO.println s!\"var: {decide (∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)}\"\n";
  std::cout << "  IO.println s!\"supp: {decide (∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0)}\"\n";
  std::cout << "  IO.println s!\"dir_nonzero: {decide (∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)}\"\n";
  std::cout << "  IO.println s!\"budget: {decide (∀ j, box.weightBudget j ≤ (box.certificate j).B)}\"\n";
  std::cout << "  IO.println s!\"weight_nonneg: {decide (∀ j i, 0 ≤ box.weightLower j i)}\"\n";
  std::cout << "  IO.println s!\"weight_pos: {decide (∀ j, ∃ i, 0 < box.weightLower j i)}\"\n";
  std::cout << "  IO.println s!\"comp_angle: {decide (box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)}\"\n";
  std::cout << "  IO.println s!\"c_core_margin: {decide (box.δ ≤ c_core)}\"\n";
  std::cout << "  IO.println s!\"core_B_pos: {decide (0 < (cbox.certificate 0).B)}\"\n";
  std::cout << "  IO.println s!\"core_var: {decide (cbox.variationRadiusSum 0 + 3 * variationError ≤ (cbox.certificate 0).B * cbox.δ)}\"\n";
  std::cout << "  IO.println s!\"core_supp: {decide (∀ i k, cbox.supportUpper 0 i k ≤ 0)}\"\n";
  std::cout << "  IO.println s!\"core_dir_nonzero: {decide (∀ i, cbox.supportUpper 0 i ((cbox.certificate 0).nonzeroWitness i) < 0)}\"\n";
  std::cout << "  IO.println s!\"core_budget: {decide (cbox.weightBudget 0 ≤ (cbox.certificate 0).B)}\"\n";
  std::cout << "  IO.println s!\"core_weight_nonneg: {decide (∀ i, 0 ≤ cbox.weightLower 0 i)}\"\n";
  std::cout << "  IO.println s!\"core_weight_pos: {decide (∃ i, 0 < cbox.weightLower 0 i)}\"\n";
  std::cout << "  IO.println s!\"core_angle: {decide (cbox.r ^ 2 * (1 + (cbox.c - cbox.δ) ^ 2) ≤ 4 * (cbox.c - cbox.δ) ^ 2)}\"\n";
  std::cout << "  IO.println s!\"c_cone_pos: {decide (0 < c_cone)}\"\n";
  std::cout << "  IO.println s!\"c_margin: {decide (box.δ ≤ box.c)}\"\n";
  std::cout << "  IO.println s!\"c_sum_pos: {decide (0 < box.c + box.δ)}\"\n";
  std::cout << "  IO.println s!\"hdecomp: {decide (cbox.approxNormalizedCenter 0 = lam • box.approxNormalizedCenter 0 + w)}\"\n";
  std::cout << "  IO.println s!\"hortho: {decide ((∑ i, box.approxNormalizedCenter 0 i * w i) = 0)}\"\n";
  std::cout << "  IO.println s!\"hmargin: {decide (0 ≤ lam * c_cone - c_core)}\"\n";
  std::cout << "  IO.println s!\"hineq: {decide ((∑ i, w i ^ 2) * ((∑ i, box.approxNormalizedCenter 0 i ^ 2) - c_cone ^ 2) ≤ (∑ i, box.approxNormalizedCenter 0 i ^ 2) * (lam * c_cone - c_core) ^ 2)}\"\n";

  return 0;
}
