#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  int indices[4] = {25, 167, 200, 203};
  for (int idx : indices) {
    const auto &ax = axes[idx];
    std::cout << "Axis " << idx << ":\n";
    std::cout << "  delta = " << ax.delta.ToDouble() << "\n";
    std::cout << "  B = " << ax.cert.B.ToDouble() << "\n";
    std::cout << "  center = (" << ax.center.x.ToDouble() << ", "
              << ax.center.y.ToDouble() << ", "
              << ax.center.z.ToDouble() << ")\n";
    std::cout << "  contacts: \n";
    for (int k = 0; k < 3; k++) {
      std::cout << "    {" << ax.cert.contacts[k].edge_start << ", "
                << ax.cert.contacts[k].edge_finish << ", "
                << ax.cert.contacts[k].edge_start2 << ", "
                << ax.cert.contacts[k].edge_finish2 << ", "
                << ax.cert.contacts[k].mix << ", "
                << ax.cert.contacts[k].vertex << "}\n";
    }
  }

  // Axis 100000:
  ContactInfo c_100k[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 0, 14}
  };
  AxisCertificate ax_100k; BigVecQ3 ctr_100k; BigRat del_100k; std::string err;
  Tube229::AuditAxis(tri, c_100k, &ax_100k, &ctr_100k, &del_100k, &err, BigRat(1, 1000));
  std::cout << "Axis 100000 (sibling mix 0):\n";
  std::cout << "  delta = " << del_100k.ToDouble() << "\n";
  std::cout << "  B = " << ax_100k.B.ToDouble() << "\n";
  std::cout << "  center = (" << ctr_100k.x.ToDouble() << ", "
            << ctr_100k.y.ToDouble() << ", "
            << ctr_100k.z.ToDouble() << ")\n";
  std::cout << "  contacts: \n";
  for (int k = 0; k < 3; k++) {
    std::cout << "    {" << c_100k[k].edge_start << ", "
              << c_100k[k].edge_finish << ", "
              << c_100k[k].edge_start2 << ", "
              << c_100k[k].edge_finish2 << ", "
              << c_100k[k].mix << ", "
              << c_100k[k].vertex << "}\n";
  }

  return 0;
}
