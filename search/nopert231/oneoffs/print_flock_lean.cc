#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

void PrintAxisLean(const std::string &name, const AxisCertificate &ax) {
  std::cout << "def " << name << " : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << ax.contacts[0].edge_start << ", "
            << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << ax.contacts[0].edge_finish << ", "
            << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", "
            << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", "
            << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << ax.contacts[0].mix << ", "
            << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "],\n";
  std::cout << "  index := ![" << ax.contacts[0].vertex << ", "
            << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << ax.nonzero_witness[0] << ", "
            << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax.B.ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  int chosen[4] = {9030, 3449, 389, 36};
  for (int m = 0; m < 4; m++) {
    PrintAxisLean("flockAx" + std::to_string(m), axes[chosen[m]].cert);
  }
  return 0;
}
