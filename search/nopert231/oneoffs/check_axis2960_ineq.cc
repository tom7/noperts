#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo contacts0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, contacts0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  int a = 2960;
  const auto &ax = valid_axes[a];
  vec3 v = vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                ax.center.z.ToDouble() / ax.cert.B.ToDouble()};

  double lam = yocto::dot(v, u0) / norm_u0_sq;
  vec3 w = v - lam * u0;
  double norm_w_sq = yocto::dot(w, w);

  double c_cone = 0.035;
  double c_core = 0.00055;

  double LHS = norm_w_sq * (norm_u0_sq - c_cone * c_cone);
  double RHS = norm_u0_sq * (lam * c_cone - c_core) * (lam * c_cone - c_core);

  std::cout << std::setprecision(10);
  std::cout << "lam = " << lam << "\n";
  std::cout << "norm_w_sq = " << norm_w_sq << "\n";
  std::cout << "norm_u0_sq = " << norm_u0_sq << "\n";
  std::cout << "LHS = " << LHS << "\n";
  std::cout << "RHS = " << RHS << "\n";
  std::cout << "hineq holds (LHS <= RHS): " << (LHS <= RHS) << "\n";
  std::cout << "Ratio RHS / LHS = " << RHS / LHS << "\n";

  return 0;
}
