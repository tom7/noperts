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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  BigVecQ3 u_norm = center0 / ax0.B;
  BigRat u_sq = BigVecQ3::Dot(u_norm, u_norm);

  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_cert, &core_center, &core_delta, &err, BigRat(0));
  BigVecQ3 v_norm = core_center / core_cert.B;

  BigRat lam = BigVecQ3::Dot(v_norm, u_norm) / u_sq;
  BigVecQ3 w = {v_norm.x - lam * u_norm.x, v_norm.y - lam * u_norm.y, v_norm.z - lam * u_norm.z};
  BigRat w_sq = BigVecQ3::Dot(w, w);

  std::cout << "lam = " << lam.ToDouble() << ", |w| = " << std::sqrt(w_sq.ToDouble()) << "\n";
  std::cout << "|u_norm| = " << std::sqrt(u_sq.ToDouble()) << ", |v_norm| = " << std::sqrt(BigVecQ3::Dot(v_norm, v_norm).ToDouble()) << "\n";
  std::cout << "core_delta = " << core_delta.ToDouble() << "\n";

  for (double c_cone_d : {0.050, 0.045, 0.042, 0.040, 0.038, 0.036, 0.035}) {
    BigRat c_cone = BigRat::FromDouble(c_cone_d);
    BigRat c_core(1, 1000); // 1e-3
    BigRat lhs = w_sq * (u_sq - c_cone * c_cone);
    BigRat margin = lam * c_cone - c_core;
    BigRat rhs = u_sq * margin * margin;
    bool pass = (margin >= BigRat(0)) && (lhs <= rhs);
    std::cout << "c_cone=" << c_cone_d << " c_core=0.001: margin=" << margin.ToDouble()
              << " hineq=" << (pass ? "PASS" : "FAIL")
              << " (lhs=" << lhs.ToDouble() << ", rhs=" << rhs.ToDouble() << ")\n";
  }


  return 0;
}
