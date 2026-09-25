#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
  BigVecQ3 u_norm = {center0.x / ax0.B, center0.y / ax0.B, center0.z / ax0.B};
  BigRat u_sq = BigVecQ3::Dot(u_norm, u_norm);
  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_cert, &core_center, &core_delta, &err, BigRat(0));
  std::cout << "core_delta = " << core_delta.ToDouble() << "\n";
  std::cout << "core B = " << core_cert.B.ToString() << "\n";



  BigVecQ3 v_norm = {core_center.x / core_cert.B, core_center.y / core_cert.B, core_center.z / core_cert.B};
  BigRat lam = BigVecQ3::Dot(v_norm, u_norm) / u_sq;
  BigVecQ3 w = {v_norm.x - lam * u_norm.x, v_norm.y - lam * u_norm.y, v_norm.z - lam * u_norm.z};
  BigRat w_sq = BigVecQ3::Dot(w, w);

  std::cout << "u_ann = (" << u_norm.x.ToDouble() << ", " << u_norm.y.ToDouble() << ", " << u_norm.z.ToDouble() << ")\n";
  std::cout << "v_core = (" << v_norm.x.ToDouble() << ", " << v_norm.y.ToDouble() << ", " << v_norm.z.ToDouble() << ")\n";
  std::cout << "axis 267: lam = " << lam.ToDouble() << ", |w| = " << std::sqrt(w_sq.ToDouble()) << "\n";

  for (double c_core_d : {0.001, 0.0005, 0.0003, 0.0001, 0.00005}) {
    BigRat c_cone(15, 1000); // 0.015
    BigRat c_core = BigRat::FromDouble(c_core_d);
    BigRat lhs = w_sq * (u_sq - c_cone * c_cone);
    BigRat margin = lam * c_cone - c_core;
    BigRat rhs = u_sq * margin * margin;
    bool pass = (margin >= BigRat(0)) && (lhs <= rhs);
    std::cout << "c_core=" << c_core_d << ": margin=" << margin.ToDouble()
              << " hineq=" << (pass ? "PASS" : "FAIL")
              << " (lhs=" << lhs.ToDouble() << ", rhs=" << rhs.ToDouble() << ")\n";
  }
  return 0;
}


