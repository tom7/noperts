#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  // Core axis from find_closest_core_axis.cc:
  ContactInfo c_core[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax_c; BigVecQ3 ctr_c; BigRat del_c;
  if (!Tube229::AuditAxis(tri, c_core, &ax_c, &ctr_c, &del_c, &err, BigRat(0))) {
    std::cout << "Audit core failed: " << err << "\n";
    return 1;
  }

  // Lean's approxNormalizedCenter 0 is ctr / B
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigVecQ3 uc = {ctr_c.x / ax_c.B, ctr_c.y / ax_c.B, ctr_c.z / ax_c.B};

  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
  BigRat uc_sq = uc.x * uc.x + uc.y * uc.y + uc.z * uc.z;

  double cos_t = dot.ToDouble() / std::sqrt(u0_sq.ToDouble() * uc_sq.ToDouble());
  double theta = std::acos(cos_t) * 180.0 / M_PI;
  std::cout << "Angle theta: " << theta << " deg\n";
  std::cout << "||u0||: " << std::sqrt(u0_sq.ToDouble()) << "\n";
  std::cout << "4/7 * ||u0||: " << (4.0 / 7.0) * std::sqrt(u0_sq.ToDouble()) << "\n";
  std::cout << "||u0|| * sin(theta): " << std::sqrt(u0_sq.ToDouble()) * std::sin(theta * M_PI / 180.0) << "\n";

  BigRat lam = dot / u0_sq;
  BigVecQ3 w = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
  std::cout << "lam: " << lam.ToDouble() << "\n";
  std::cout << "w: (" << w.x.ToDouble() << ", " << w.y.ToDouble() << ", " << w.z.ToDouble() << ")\n";
  std::cout << "ortho check: " << (u0.x * w.x + u0.y * w.y + u0.z * w.z).ToDouble() << "\n";

  return 0;
}
