#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int N = base_axes.size();
  std::cout << "Total base axes: " << N << "\n";

  std::vector<int> robust;
  std::string err;
  for (int i = 0; i < N; i++) {
    BigRat var_radius;
    AxisCertificate ax;
    BigVecQ3 cnt;
    if (!Tube229::AuditAxis(tri, base_axes[i].cert.contacts, &ax, &cnt, &var_radius, &err, BigRat(5, 1000))) continue;
    if (ax.B.ToDouble() < 0.05) continue;
    double var_ratio = var_radius.ToDouble() / ax.B.ToDouble();
    if (var_ratio <= 0.000234013) {
      robust.push_back(i);
    }
  }
  std::cout << "Found " << robust.size() << " robust axes with B >= 0.05 and var_ratio <= 0.000234!\n";
  return 0;
}
