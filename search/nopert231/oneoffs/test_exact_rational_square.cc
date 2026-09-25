#include <iostream>
#include <vector>
#include <cmath>
#include <set>
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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  std::cout << "u0 = (" << u0.x.ToString() << ", " << u0.y.ToString() << ", " << u0.z.ToString() << ")\n";

  // u0 dot u0:
  BigRat norm_u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  std::cout << "norm_u0_sq = " << norm_u0_sq.ToString() << " (" << norm_u0_sq.ToDouble() << ")\n";

  // Center point P0 in plane <x, u0> = 1:
  // P0 = u0 / norm_u0_sq
  BigVecQ3 P0 = {u0.x / norm_u0_sq, u0.y / norm_u0_sq, u0.z / norm_u0_sq};

  // Find exact rational E1 perp to u0:
  // u0.x * E1.x + u0.y * E1.y + u0.z * E1.z = 0
  // Choose E1 = (-u0.y, u0.x, 0)
  BigVecQ3 E1 = {-u0.y, u0.x, BigRat(0)};
  BigRat E1_sq = E1.x * E1.x + E1.y * E1.y + E1.z * E1.z;

  // Choose E2 = cross(u0, E1):
  // E2 = (u0.y * 0 - u0.z * u0.x, u0.z * (-u0.y) - u0.x * 0, u0.x * u0.x - u0.y * (-u0.y))
  //    = (-u0.z * u0.x, -u0.z * u0.y, u0.x * u0.x + u0.y * u0.y)
  BigVecQ3 E2 = {-u0.z * u0.x, -u0.z * u0.y, u0.x * u0.x + u0.y * u0.y};
  BigRat E2_sq = E2.x * E2.x + E2.y * E2.y + E2.z * E2.z;

  std::cout << "E1_sq = " << E1_sq.ToDouble() << ", E2_sq = " << E2_sq.ToDouble() << "\n";

  // Cone radius R:
  // R^2 = 1/c_cone^2 - 1/norm_u0_sq
  // For c_cone = 20/1000 = 1/50: 1/c_cone^2 = 2500
  BigRat c_cone(1, 50);
  BigRat R_sq = BigRat(2500, 1) - BigRat(1, 1) / norm_u0_sq;
  std::cout << "R_sq = " << R_sq.ToDouble() << " (R = " << std::sqrt(R_sq.ToDouble()) << ")\n";

  // We want R1 such that E1_sq * R1^2 >= R^2:
  // R1 >= R / sqrt(E1_sq)
  // Let's compute R1 and R2:
  double R_val = std::sqrt(R_sq.ToDouble());
  double R1_val = R_val / std::sqrt(E1_sq.ToDouble());
  double R2_val = R_val / std::sqrt(E2_sq.ToDouble());

  // Round up to nice rationals (integers or halves):
  BigRat R1(std::ceil(R1_val * 1.01));
  BigRat R2(std::ceil(R2_val * 1.01));
  std::cout << "R1 = " << R1.ToString() << " (min " << R1_val << ")\n";
  std::cout << "R2 = " << R2.ToString() << " (min " << R2_val << ")\n";

  // Verify:
  if (E1_sq * R1 * R1 >= R_sq && E2_sq * R2 * R2 >= R_sq) {
    std::cout << "R1 and R2 rigorously circumscribe the cone disk!\n";
  } else {
    std::cout << "ERROR: bounds too small!\n";
    return 1;
  }

  // Define the 4 corners of the circumscribed rectangle:
  // V0 = P0 + R1*E1 - R2*E2
  // V1 = P0 + R1*E1 + R2*E2
  // V2 = P0 - R1*E1 + R2*E2
  // V3 = P0 - R1*E1 - R2*E2
  BigVecQ3 V[4] = {
    {P0.x + R1 * E1.x - R2 * E2.x, P0.y + R1 * E1.y - R2 * E2.y, P0.z + R1 * E1.z - R2 * E2.z},
    {P0.x + R1 * E1.x + R2 * E2.x, P0.y + R1 * E1.y + R2 * E2.y, P0.z + R1 * E1.z + R2 * E2.z},
    {P0.x - R1 * E1.x + R2 * E2.x, P0.y - R1 * E1.y + R2 * E2.y, P0.z - R1 * E1.z + R2 * E2.z},
    {P0.x - R1 * E1.x - R2 * E2.x, P0.y - R1 * E1.y - R2 * E2.y, P0.z - R1 * E1.z - R2 * E2.z}
  };

  // Check the 4 triangles S0, S1, S2, S3:
  // S_k = triangle(P0, V_k, V_{(k+1)%4})
  BigRat c_core(1, 2000); // 0.0005
  BigRat c_core_sq = c_core * c_core;

  auto check_vertex = [&](const BigVecQ3& p, size_t a) -> bool {
    BigVecQ3 v = axes[a].center;
    BigRat B = axes[a].cert.B;
    // v_normalized = v / B
    // inner(p, v/B) >= c_core * ||p||
    // inner(p, v) >= c_core * B * ||p||
    BigRat dot = p.x * v.x + p.y * v.y + p.z * v.z;
    if (dot <= BigRat(0)) return false;
    BigRat p_sq = p.x * p.x + p.y * p.y + p.z * p.z;
    // dot^2 >= c_core^2 * B^2 * p_sq
    return (dot * dot >= c_core_sq * B * B * p_sq);
  };

  auto check_tri = [&](const BigVecQ3& p1, const BigVecQ3& p2, const BigVecQ3& p3) -> int {
    for (size_t a = 0; a < axes.size(); a++) {
      if (check_vertex(p1, a) && check_vertex(p2, a) && check_vertex(p3, a)) {
        return (int)a;
      }
    }
    return -1;
  };

  int leaf_count = 0;
  std::set<int> used_axes;

  auto subdivide = [&](auto& self, const BigVecQ3& p1, const BigVecQ3& p2, const BigVecQ3& p3, int depth) -> bool {
    int a = check_tri(p1, p2, p3);
    if (a >= 0) {
      leaf_count++;
      used_axes.insert(a);
      return true;
    }
    if (depth >= 8) return false;
    BigVecQ3 m12 = {(p1.x + p2.x) / BigRat(2), (p1.y + p2.y) / BigRat(2), (p1.z + p2.z) / BigRat(2)};
    BigVecQ3 m23 = {(p2.x + p3.x) / BigRat(2), (p2.y + p3.y) / BigRat(2), (p2.z + p3.z) / BigRat(2)};
    BigVecQ3 m31 = {(p3.x + p1.x) / BigRat(2), (p3.y + p1.y) / BigRat(2), (p3.z + p1.z) / BigRat(2)};
    return self(self, p1, m12, m31, depth + 1) &&
           self(self, m12, p2, m23, depth + 1) &&
           self(self, m31, m23, p3, depth + 1) &&
           self(self, m23, m31, m12, depth + 1);
  };

  bool all_ok = true;
  for (int k = 0; k < 4; k++) {
    if (!subdivide(subdivide, P0, V[k], V[(k + 1) % 4], 0)) {
      all_ok = false;
      std::cout << "Failed on sector " << k << "!\n";
      break;
    }
  }

  std::cout << "Exact rational square: all_ok=" << all_ok
            << ", total_leaves=" << leaf_count
            << ", used_axes=" << used_axes.size() << "\n";
  std::cout << "Axes: ";
  for (int a : used_axes) std::cout << a << " ";
  std::cout << "\n";

  return 0;
}
