#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static void EmitLeanAxis(const std::string &name, const AxisCertificate &ax) {
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
  std::cout << "  B := " << ax.B.Numerator().ToString() << "/" << ax.B.Denominator().ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int chosen[3] = {0, 24, 210};
  std::string names[3] = {"ax1", "ax2", "ax3"};

  for (int k = 0; k < 3; k++) {
    int idx = chosen[k];
    std::cout << "-- Axis index " << idx << ", delta = " << axes[idx].delta.ToDouble() << "\n";
    EmitLeanAxis(names[k], axes[idx].cert);
  }

  return 0;
}
