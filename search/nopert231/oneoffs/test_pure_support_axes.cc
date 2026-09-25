#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto all_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int zero_defect_count = 0;
  std::string err;
  for (int i = 0; i < 100; i++) {
    AxisCertificate ax;
    BigVecQ3 cnt;
    BigRat var;
    if (Tube229::AuditAxis(tri, all_axes[i].cert.contacts, &ax, &cnt, &var, &err, BigRat(0))) {
      zero_defect_count++;
    }
  }
  std::cout << "Out of first 100 hull support axes, " << zero_defect_count << " have EXACT ZERO DEFECT!\n";
  return 0;
}
