#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

void PrintAxis(int idx, const Tube229::AuditedAxis &ax) {
  std::cout << "-- Axis index " << idx << ", delta = " << ax.delta.ToDouble() << "\n";
  std::cout << "def ax1 : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << ax.cert.contacts[0].edge_start << ", "
                                  << ax.cert.contacts[1].edge_start << ", "
                                  << ax.cert.contacts[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << ax.cert.contacts[0].edge_finish << ", "
                                   << ax.cert.contacts[1].edge_finish << ", "
                                   << ax.cert.contacts[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << ax.cert.contacts[0].edge_start2 << ", "
                                    << ax.cert.contacts[1].edge_start2 << ", "
                                    << ax.cert.contacts[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << ax.cert.contacts[0].edge_finish2 << ", "
                                     << ax.cert.contacts[1].edge_finish2 << ", "
                                     << ax.cert.contacts[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << ax.cert.contacts[0].mix << ", "
                             << ax.cert.contacts[1].mix << ", "
                             << ax.cert.contacts[2].mix << "],\n";
  std::cout << "  index := ![" << ax.cert.contacts[0].vertex << ", "
                               << ax.cert.contacts[1].vertex << ", "
                               << ax.cert.contacts[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << ax.cert.nonzero_witness[0] << ", "
                                        << ax.cert.nonzero_witness[1] << ", "
                                        << ax.cert.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax.cert.B.ToString() << "\n";
  std::cout << "}\n";
  std::cout << "delta rational: " << ax.delta.ToString() << "\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  PrintAxis(23, axes[23]);
  return 0;
}
