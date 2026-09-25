#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

void EmitLeanAxis(const std::string &name, const AxisCertificate &ax, const BigRat &del) {
  std::cout << "-- delta = " << del.ToDouble() << " = " << del.Numerator().ToString() << " / " << del.Denominator().ToString() << "\n";
  std::cout << "def " << name << " : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << (int)ax.contacts[0].edge_start << ", "
                                  << (int)ax.contacts[1].edge_start << ", "
                                  << (int)ax.contacts[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << (int)ax.contacts[0].edge_finish << ", "
                                   << (int)ax.contacts[1].edge_finish << ", "
                                   << (int)ax.contacts[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << (int)ax.contacts[0].edge_start2 << ", "
                                   << (int)ax.contacts[1].edge_start2 << ", "
                                   << (int)ax.contacts[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << (int)ax.contacts[0].edge_finish2 << ", "
                                    << (int)ax.contacts[1].edge_finish2 << ", "
                                    << (int)ax.contacts[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << ax.contacts[0].mix << ", "
                             << ax.contacts[1].mix << ", "
                             << ax.contacts[2].mix << "],\n";
  std::cout << "  index := ![" << (int)ax.contacts[0].vertex << ", "
                               << (int)ax.contacts[1].vertex << ", "
                               << (int)ax.contacts[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << (int)ax.nonzero_witness[0] << ", "
                                        << (int)ax.nonzero_witness[1] << ", "
                                        << (int)ax.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax.B.Numerator().ToString() << " / " << ax.B.Denominator().ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  std::cout << "import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate\n";
  std::cout << "open Noperthedron Noperthedron.Nopert229\n\n";

  // Unique axes used: 167, 179, 206, and sibling 100300
  EmitLeanAxis("coreAx0", axes[167].cert, axes[167].delta);
  EmitLeanAxis("coreAx1", axes[179].cert, axes[179].delta);
  EmitLeanAxis("coreAx2", axes[206].cert, axes[206].delta);

  ContactInfo c_100300[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 300, 14}
  };
  AxisCertificate ax_sib; BigVecQ3 ctr_sib; BigRat del_sib; std::string err;
  Tube229::AuditAxis(tri, c_100300, &ax_sib, &ctr_sib, &del_sib, &err, BigRat(1, 1000));
  EmitLeanAxis("coreAx3", ax_sib, del_sib);

  return 0;
}
