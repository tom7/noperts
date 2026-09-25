#include <iostream>
#include <string>
#include <vector>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

int main() {
  std::vector<std::string> target_paths = {
    "3121300",
    "3121303021",
    "3121303022",
    "3121303023",
    "3121303200",
    "312130332"
  };

  for (const auto &p : target_paths) {
    TriangleQ tri = TriangleFromPath(p);
    std::cout << "\nPath " << p << " (depth " << p.size() << "):\n";
    // Check how many axes can be audited with defect <= 0
    // We can run FindHullSupportAxis or see candidate axes
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    bool has_hull = Tube229::FindHullSupportAxis(tri, &cert, &center, &delta, &fail);
    std::cout << "  FindHullSupportAxis: " << (has_hull ? "FOUND" : ("FAIL: " + fail)) << "\n";
    if (has_hull) {
      std::cout << "  Center: (" << center.x.ToDouble() << ", " << center.y.ToDouble() << ", " << center.z.ToDouble() << ")\n";
      std::cout << "  B: " << cert.B.ToString() << ", delta: " << delta.ToString() << "\n";
    }
  }
  return 0;
}
