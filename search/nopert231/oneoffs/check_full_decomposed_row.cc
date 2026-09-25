#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static BigRat Sq(const BigRat &x) { return x * x; }

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Axis 0 (Annular axis)
  ContactInfo c_ann[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c_ann, &cert0, &center0, &delta0, &err, BigRat(5, 1000));

  // Core axis: Axis 1691
  ContactInfo c_core[3] = {{15, 19, 19, 3, 900, 19}, {3, 2, 2, 1, 333, 2}, {4, 8, 8, 9, 1000, 8}};
  AxisCertificate cert_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  Tube229::AuditAxis(tri, c_core, &cert_core, &center_core, &delta_core, &err, BigRat(0));

  BigRat r = BigRat(1, 2000);
  BigRat r_min = BigRat(1, 10000);
  BigRat c_cone = BigRat(42, 1000); // 0.042
  BigRat c_core = BigRat(1, 1000);
  BigRat box_c = BigRat(1, 1000);
  BigRat box_delta = BigRat(1, 100000); // 1e-5

  BigVecQ3 u0 = {center0.x / cert0.B, center0.y / cert0.B, center0.z / cert0.B};
  BigVecQ3 v = {center_core.x / cert_core.B, center_core.y / cert_core.B, center_core.z / cert_core.B};

  BigRat u0_sq = Sq(u0.x) + Sq(u0.y) + Sq(u0.z);
  BigRat dot_u0_v = u0.x * v.x + u0.y * v.y + u0.z * v.z;
  BigRat lam = dot_u0_v / u0_sq;
  BigVecQ3 w = {v.x - lam * u0.x, v.y - lam * u0.y, v.z - lam * u0.z};
  BigRat w_sq = Sq(w.x) + Sq(w.y) + Sq(w.z);

  std::cout << "lam = " << lam.ToDouble() << "\n";
  std::cout << "u0_sq = " << u0_sq.ToDouble() << "\n";
  std::cout << "w_sq = " << w_sq.ToDouble() << "\n";

  // Check 1: lam >= 0
  std::cout << "hlam_nonneg: " << (lam >= BigRat(0) ? "OK" : "FAIL") << "\n";

  // Check 2: c_cone >= 0
  std::cout << "hc_cone_nonneg: " << (c_cone >= BigRat(0) ? "OK" : "FAIL") << "\n";

  // Check 3: margin = lam * c_cone - c_core >= 0
  BigRat margin = lam * c_cone - c_core;
  std::cout << "hmargin: " << (margin >= BigRat(0) ? "OK" : "FAIL") << " (margin = " << margin.ToDouble() << ")\n";

  // Check 4: Projection inequality hineq:
  // w_sq * (u0_sq - c_cone^2) <= u0_sq * margin^2
  BigRat lhs = w_sq * (u0_sq - Sq(c_cone));
  BigRat rhs = u0_sq * Sq(margin);
  std::cout << "hineq: " << (lhs <= rhs ? "OK" : "FAIL")
            << " (lhs = " << lhs.ToDouble() << ", rhs = " << rhs.ToDouble() << ")\n";

  // Check 5: annular_dominance:
  // ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4)*r^2) * ((c_cone - delta)^2 * B0^2)
  BigRat D0 = BigRat(2, 10000000); // 2e-7 vertex defect budget
  BigRat ann_lhs = Sq(BigRat(1, 2) * Sq(r) * cert0.B + D0);
  BigRat ann_rhs = Sq(r_min) * (BigRat(1, 1) - BigRat(1, 4) * Sq(r)) * Sq((c_cone - box_delta) * cert0.B);
  std::cout << "annular_dominance: " << (ann_lhs <= ann_rhs ? "OK" : "FAIL")
            << " (ann_lhs = " << ann_lhs.ToDouble() << ", ann_rhs = " << ann_rhs.ToDouble() << ")\n";

  return 0;
}
