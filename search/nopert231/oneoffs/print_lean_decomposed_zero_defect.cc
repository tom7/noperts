#include <iostream>
#include <fstream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

static std::string LeanRat(const BigRat &r) {
  const auto &[numer, denom] = r.Parts();
  return numer.ToString() + " / " + denom.ToString();
}

static void PrintLeanAxis(std::ostream &os, const std::string &name, const AxisCertificate &ax) {
  os << "def " << name << " : AxisCertificate := {\n";
  os << "  edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "],\n";
  os << "  edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "],\n";
  os << "  edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "],\n";
  os << "  edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "],\n";
  os << "  mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "],\n";
  os << "  index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "],\n";
  os << "  nonzeroWitness := ![" << std::max(0, ax.nonzero_witness[0]) << ", "
                            << std::max(0, ax.nonzero_witness[1]) << ", "
                            << std::max(0, ax.nonzero_witness[2]) << "],\n";
  os << "  B := " << LeanRat(ax.B) << "\n";
  os << "}\n\n";
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Zero-defect annular axis:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));

  // Complement axes:
  ContactInfo comp0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(14, 15, 15, 19, 600, 15)
  };
  ContactInfo comp1[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 600, 8),
    MakeContact(14, 15, 15, 19, 200, 15)
  };
  ContactInfo comp2[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(10, 15, 15, 19, 600, 15),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_comp[3];
  BigVecQ3 ctr_comp[3];
  BigRat del_comp[3];
  Tube229::AuditAxis(tri, comp0, &ax_comp[0], &ctr_comp[0], &del_comp[0], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp1, &ax_comp[1], &ctr_comp[1], &del_comp[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp2, &ax_comp[2], &ctr_comp[2], &del_comp[2], &err, BigRat(0));

  // Winning core axis (Axis #3077):
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 0, 2),
    MakeContact(4, 8, 8, 9, 666, 8),
    MakeContact(15, 19, 19, 3, 1000, 19)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

  BigVecQ3 u_ann = {ctr_ann.x / ax_ann.B, ctr_ann.y / ax_ann.B, ctr_ann.z / ax_ann.B};
  BigRat u0_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  BigVecQ3 u_core = {ctr_core.x / ax_core.B, ctr_core.y / ax_core.B, ctr_core.z / ax_core.B};
  BigRat dot = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
  BigRat lam = dot / u0_sq;
  BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};

  std::ofstream out("/home/tom/nopert-project/Noperthedron/Noperthedron/Nopert229/ManualDecomposedTest.lean");
  out << "module\n\n";
  out << "public import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate\n";
  out << "public import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate\n";
  out << "public import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree\n\n";
  out << "@[expose] public section\n\n";
  out << "namespace Noperthedron.Nopert229.AtlasProjectiveLocalCertificate\n\n";

  PrintLeanAxis(out, "ax0", ax_ann);
  PrintLeanAxis(out, "ax1", ax_comp[0]);
  PrintLeanAxis(out, "ax2", ax_comp[1]);
  PrintLeanAxis(out, "ax3", ax_comp[2]);
  PrintLeanAxis(out, "coreAx", ax_core);

  out << "def testBox : Box := {\n";
  out << "  interval := AtlasPose.rootInterval ℚ,\n";
  out << "  root := 0,\n";
  out << "  triangle := fun i c => (![\n";
  for (int c = 0; c < 3; c++) {
    out << "    ![" << LeanRat(tri.corners[c].x) << ", "
        << LeanRat(tri.corners[c].y) << ", "
        << LeanRat(tri.corners[c].z) << "]"
        << (c < 2 ? "," : "") << "\n";
  }
  out << "  ] : Fin 3 → Fin 3 → ℚ) i c,\n";
  out << "  chart := 0,\n";
  out << "  symmetryIndex := 0,\n";
  out << "  certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,\n";
  out << "  c := 18 / 10000,\n";
  out << "  δ := 13 / 10000,\n";
  out << "  r := 1 / 2000\n";
  out << "}\n\n";

  out << "def testLam : ℚ := " << LeanRat(lam) << "\n\n";
  out << "def testW : Fin 3 → ℚ := !["
      << LeanRat(w.x) << ", "
      << LeanRat(w.y) << ", "
      << LeanRat(w.z) << "]\n\n";

  out << "def testDefect0 : Fin 3 → ℚ := ![0, 0, 0]\n\n";
  out << "def testD0 : ℚ := 0\n\n";

  out << "#eval testBox.DecomposedViewValid coreAx testDefect0 testD0 (1 / 10000) (133 / 10000) (18 / 10000) testLam testW\n\n";
  out << "theorem testDecomposedValid :\n";
  out << "  testBox.DecomposedViewValid coreAx testDefect0 testD0 (1 / 10000) (133 / 10000) (18 / 10000) testLam testW := by\n";
  out << "  decide\n";

  out.close();
  std::cout << "Wrote ManualDecomposedTest.lean successfully.\n";

  return 0;
}
