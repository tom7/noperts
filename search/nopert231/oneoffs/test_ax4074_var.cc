#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  auto a = base_axes[4074];
  AxisCertificate ax;
  BigVecQ3 cnt;
  BigRat var_radius;
  std::string err;
  bool ok = Tube229::AuditAxis(tri, a.cert.contacts, &ax, &cnt, &var_radius, &err, BigRat(5, 1000));
  std::cout << "Audit ok: " << ok << "\n";
  std::cout << "B = " << ax.B.ToString() << " (" << ax.B.ToDouble() << ")\n";
  std::cout << "var_radius = " << var_radius.ToString() << " (" << var_radius.ToDouble() << ")\n";
  std::cout << "var_radius / B = " << (var_radius.ToDouble() / ax.B.ToDouble()) << "\n";
  std::cout << "delta = 0.000234013\n";
  return 0;
}
