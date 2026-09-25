#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Complement axes from tree_0.json:
  ContactInfo c_comp[3][3] = {
    {
      {15, 19, 19, 3, 200, 19},
      {2, 1, 1, 4, 200, 1},
      {8, 9, 9, 10, 200, 9}
    },
    {
      {2, 1, 1, 4, 0, 1},
      {10, 15, 15, 19, 333, 15},
      {10, 15, 15, 19, 0, 15}
    },
    {
      {3, 2, 2, 1, 800, 2},
      {4, 8, 8, 9, 800, 8},
      {14, 15, 15, 19, 800, 15}
    }
  };

  for (int a = 0; a < 3; a++) {
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    bool ok = Tube229::AuditAxis(tri, c_comp[a], &cert, &center, &delta, &err, BigRat(0));
    std::cout << "Comp axis " << a << ": " << (ok ? "PASSED" : "FAILED: " + err) << "\n";
  }

  // Inner core axis from tree_0.json:
  ContactInfo c_core[3] = {
    {2, 1, 1, 4, 0, 1},
    {14, 15, 15, 19, 500, 15},
    {2, 1, 1, 4, 500, 1}
  };
  AxisCertificate cert_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  bool ok_core = Tube229::AuditAxis(tri, c_core, &cert_core, &center_core, &delta_core, &err, BigRat(0));
  std::cout << "Inner core axis: " << (ok_core ? "PASSED" : "FAILED: " + err) << "\n";

  return 0;
}
