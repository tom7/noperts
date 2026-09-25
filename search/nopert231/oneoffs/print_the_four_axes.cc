#include <iostream>
#include <vector>
#include <cmath>
#include "base/stringprintf.h"
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  std::vector<std::string> desc;

  for (int m1 = 0; m1 <= 1000; m1 += 25) {
    for (int m2 = 0; m2 <= 1000; m2 += 25) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({cert, ctr, del});
          desc.push_back(StringPrintf("grid {2,1,1,4,0,1}, {10,15,15,19,%d,15}, {3,2,2,1,%d,2}", m1, m2));
        }
      }
    }
  }

  int hull_start = valid_axes.size();
  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  for (size_t i = 0; i < hull_axes.size(); i++) {
    const auto &ax = hull_axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      valid_axes.push_back(ax);
      desc.push_back(StringPrintf("hull_axis %d", (int)i));
    }
  }

  int chosen[4] = {4055, 157, 480, 0};
  for (int idx = 0; idx < 4; idx++) {
    int a = chosen[idx];
    std::cout << "=== Axis " << idx << " (global index " << a << ") ===\n";
    std::cout << "Description: " << desc[a] << "\n";
    std::cout << "Contacts:\n";
    for (int c = 0; c < 3; c++) {
      const auto &ci = valid_axes[a].cert.contacts[c];
      std::cout << "  {" << ci.edge_start << ", " << ci.edge_finish << ", "
                << ci.edge_start2 << ", " << ci.edge_finish2 << ", "
                << ci.mix << ", " << ci.vertex << "}\n";
    }
    std::cout << "B: " << valid_axes[a].cert.B.ToString() << "\n";
    std::cout << "center: (" << valid_axes[a].center.x.ToString() << ", "
              << valid_axes[a].center.y.ToString() << ", "
              << valid_axes[a].center.z.ToString() << ")\n";
    std::cout << "delta: " << valid_axes[a].delta.ToString() << " ("
              << valid_axes[a].delta.ToDouble() << ")\n";
    std::cout << "nonzero_witness: (" << valid_axes[a].cert.nonzero_witness[0] << ", "
              << valid_axes[a].cert.nonzero_witness[1] << ", "
              << valid_axes[a].cert.nonzero_witness[2] << ")\n";
    std::cout << "\n";
  }

  return 0;
}
