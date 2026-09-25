#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static void PrintLeanAxis(const std::string &name, const AxisCertificate &ax) {
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

  PrintLeanAxis("flockAx0", axes[9030].cert);
  PrintLeanAxis("flockAx1", axes[177].cert);
  PrintLeanAxis("flockAx2", axes[23].cert);

  std::cout << "-- Deltas:\n";
  std::cout << "-- flockAx0: " << axes[9030].delta.Numerator().ToString() << " / " << axes[9030].delta.Denominator().ToString()
            << " (" << axes[9030].delta.ToDouble() << ")\n";
  std::cout << "-- flockAx1: " << axes[177].delta.Numerator().ToString() << " / " << axes[177].delta.Denominator().ToString()
            << " (" << axes[177].delta.ToDouble() << ")\n";
  std::cout << "-- flockAx2: " << axes[23].delta.Numerator().ToString() << " / " << axes[23].delta.Denominator().ToString()
            << " (" << axes[23].delta.ToDouble() << ")\n";

  return 0;
}
