#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Total base axes: " << base_axes.size() << "\n";
  auto a = base_axes[4074];
  std::cout << "Axis 4074: B = " << a.cert.B.ToString() << " (" << a.cert.B.ToDouble() << ")\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  contact " << i << ": edgeStart=" << a.cert.contacts[i].edge_start
              << " edgeFinish=" << a.cert.contacts[i].edge_finish
              << " edgeStart2=" << a.cert.contacts[i].edge_start2
              << " edgeFinish2=" << a.cert.contacts[i].edge_finish2
              << " mix=" << a.cert.contacts[i].mix
              << " vertex=" << a.cert.contacts[i].vertex
              << " witness=" << a.cert.nonzero_witness[i] << "\n";
  }
  return 0;
}
