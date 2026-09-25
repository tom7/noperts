#include <iostream>
#include <iomanip>
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

struct AxisInfo {
  ContactInfo contacts[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 dir;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // 1. Audit coreAxis:
  ContactInfo core_c[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  if (!Tube229::AuditAxis(tri, core_c, &core_cert, &core_center, &core_delta, &err, BigRat(0))) {
    std::cout << "coreAxis audit failed: " << err << "\n";
    return 1;
  }

  // 2. Harvest zero-defect candidates:
  std::vector<AxisInfo> pool;
  int N = 80;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto candidates = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : candidates) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        BigVecQ3 u_ex = center / cert.B;
        vec3 u_vec = yocto::normalize(vec3{u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()});
        AxisInfo info;
        info.contacts[0] = contacts[0];
        info.contacts[1] = contacts[1];
        info.contacts[2] = contacts[2];
        info.cert = cert;
        info.center = center;
        info.delta = delta;
        info.dir = u_vec;
        pool.push_back(info);
      }
    }
  }

  std::cout << "Testing Axis 4757 (and all enclosed axes) for Lean annular decomposition...\n";

  // Lean parameters:
  BigRat c_cone(80, 1000); // 0.080 - 4.5 degrees
  BigRat c_core(3, 10000);  // 0.0003

  for (int idx : {4757, 3908, 1079, 2990, 1201, 1911, 4507}) {
    if (idx >= (int)pool.size()) continue;
    const auto &ax0 = pool[idx];

    BigVecQ3 u = ax0.center / ax0.cert.B;
    BigVecQ3 v = core_center / core_cert.B;

    BigRat u_sq = u.x * u.x + u.y * u.y + u.z * u.z;
    BigRat u_dot_v = u.x * v.x + u.y * v.y + u.z * v.z;

    BigRat lam = u_dot_v / u_sq;
    BigVecQ3 w = {v.x - lam * u.x, v.y - lam * u.y, v.z - lam * u.z};
    BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

    // Check hortho:
    BigRat dot_u_w = u.x * w.x + u.y * w.y + u.z * w.z;

    // Check hmargin:
    BigRat margin = lam * c_cone - c_core;

    // Check hineq:
    // (∑ w^2) * ((∑ u^2) - c_cone^2) ≤ (∑ u^2) * (lam * c_cone - c_core)^2
    BigRat lhs = w_sq * (u_sq - c_cone * c_cone);
    BigRat rhs = u_sq * (margin * margin);

    double angle = std::acos(std::clamp(u_dot_v.ToDouble() / std::sqrt(u_sq.ToDouble() * (v.x * v.x + v.y * v.y + v.z * v.z).ToDouble()), -1.0, 1.0)) * 180.0 / M_PI;

    std::cout << "\nAxis " << idx << " (angle = " << angle << " deg):\n";
    std::cout << "  lam = " << lam.ToDouble() << "\n";
    std::cout << "  w_sq = " << w_sq.ToDouble() << "\n";
    std::cout << "  ortho error = " << dot_u_w.ToDouble() << "\n";
    std::cout << "  margin = " << margin.ToDouble() << " (≥ 0: " << (margin >= 0) << ")\n";
    std::cout << "  hineq LHS = " << lhs.ToDouble() << "\n";
    std::cout << "  hineq RHS = " << rhs.ToDouble() << "\n";
    std::cout << "  hineq holds (LHS ≤ RHS): " << (lhs <= rhs) << "\n";

    if (lhs <= rhs && margin >= 0) {
      std::cout << "  SUCCESS! Axis " << idx << " satisfies ALL annular decomposition conditions!\n";
    }
  }

  return 0;
}
