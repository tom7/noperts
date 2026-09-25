#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

void PrintRat(const BigRat &r) {
  std::cout << r.GetNum().ToString() << " / " << r.GetDen().ToString();
}

void PrintAxisCert(const std::string &name, const AxisCertificate &ax, const BigVecQ3 &ctr, const BigRat &del) {
  std::cout << "def " << name << " : AxisCertificate := {\n";
  std::cout << "  B := "; PrintRat(ax.B); std::cout << ",\n";
  std::cout << "  contacts := fun\n";
  for (int k = 0; k < 3; k++) {
    std::cout << "    | " << k << " => { "
              << "edge_start := " << ax.contacts[k].edge_start << ", "
              << "edge_finish := " << ax.contacts[k].edge_finish << ", "
              << "edge_start2 := " << ax.contacts[k].edge_start2 << ", "
              << "edge_finish2 := " << ax.contacts[k].edge_finish2 << ", "
              << "mix := " << ax.contacts[k].mix << ", "
              << "vertex := " << ax.contacts[k].vertex << " }\n";
  }
  std::cout << "  nonzeroWitness := fun\n";
  for (int k = 0; k < 3; k++) {
    std::cout << "    | " << k << " => " << (int)ax.nonzeroWitness[k] << "\n";
  }
  std::cout << "  weightLowerBound := fun\n";
  for (int k = 0; k < 3; k++) {
    std::cout << "    | " << k << " => "; PrintRat(ax.weightLowerBound[k]); std::cout << "\n";
  }
  std::cout << "  weightUpperBound := fun\n";
  for (int k = 0; k < 3; k++) {
    std::cout << "    | " << k << " => "; PrintRat(ax.weightUpperBound[k]); std::cout << "\n";
  }
  std::cout << "  center := { x := "; PrintRat(ctr.x);
  std::cout << ", y := "; PrintRat(ctr.y);
  std::cout << ", z := "; PrintRat(ctr.z); std::cout << " }\n";
  std::cout << "}\n\n";

  std::cout << "-- delta for " << name << " = " << del.ToDouble() << " = ";
  PrintRat(del); std::cout << "\n\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  PrintAxisCert("core_ax0", axes[167].cert, axes[167].center, axes[167].delta);
  PrintAxisCert("core_ax1", axes[179].cert, axes[179].center, axes[179].delta);
  PrintAxisCert("core_ax2", axes[206].cert, axes[206].center, axes[206].delta);

  // Axis 100300:
  ContactInfo c_100300[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 300, 14}
  };
  AxisCertificate ax_sib; BigVecQ3 ctr_sib; BigRat del_sib; std::string err;
  Tube229::AuditAxis(tri, c_100300, &ax_sib, &ctr_sib, &del_sib, &err, BigRat(1, 1000));
  PrintAxisCert("core_ax3", ax_sib, ctr_sib, del_sib);

  return 0;
}
