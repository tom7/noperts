#include <iostream>
#include <vector>
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
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Zero defect annular axis:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };

  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  if (!Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0))) {
    std::cout << "Audit failed for annular axis: " << err << "\n";
    return 1;
  }

  BigVecQ3 u_ann = {ctr_ann.x / ax_ann.B, ctr_ann.y / ax_ann.B, ctr_ann.z / ax_ann.B};
  BigRat u0_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  double u0_norm = std::sqrt(u0_sq.ToDouble());
  std::cout << "u0_norm = " << u0_norm << "\n";

  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Found " << axes.size() << " audited hull support axes.\n";

  int num_pass = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i].cert;
    const auto &ctr = axes[i].center;
    const auto &del = axes[i].delta;

    BigVecQ3 u_core = {ctr.x / ax.B, ctr.y / ax.B, ctr.z / ax.B};
    BigRat dot = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
    BigRat lam = dot / u0_sq;
    if (lam <= 0) continue;

    BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};
    BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

    // Sweep c_cone from 0.005 to u0_norm
    for (double c_c = 0.005; c_c < u0_norm; c_c += 0.0005) {
      BigRat c_cone = BigRat::FromDouble(c_c);
      BigRat c_core = del + BigRat(1, 1000); // safety margin
      if (c_cone <= del) continue;

      BigRat margin = lam * c_cone - c_core;
      if (margin <= 0) continue;

      BigRat lhs = w_sq * (u0_sq - c_cone * c_cone);
      BigRat rhs = u0_sq * margin * margin;
      if (lhs <= rhs) {
        num_pass++;
        std::cout << "FOUND PASSING CORE AXIS! Axis #" << i
                  << " c_cone=" << c_c << " lhs=" << lhs.ToDouble()
                  << " rhs=" << rhs.ToDouble() << "\n";
        std::cout << "Contacts: {"
                  << axes[i].cert.contacts[0].edge_start << ", " << axes[i].cert.contacts[0].edge_finish << ", "
                  << axes[i].cert.contacts[0].edge_start2 << ", " << axes[i].cert.contacts[0].edge_finish2 << ", "
                  << axes[i].cert.contacts[0].mix << ", " << axes[i].cert.contacts[0].vertex << "}, {"
                  << axes[i].cert.contacts[1].edge_start << ", " << axes[i].cert.contacts[1].edge_finish << ", "
                  << axes[i].cert.contacts[1].edge_start2 << ", " << axes[i].cert.contacts[1].edge_finish2 << ", "
                  << axes[i].cert.contacts[1].mix << ", " << axes[i].cert.contacts[1].vertex << "}, {"
                  << axes[i].cert.contacts[2].edge_start << ", " << axes[i].cert.contacts[2].edge_finish << ", "
                  << axes[i].cert.contacts[2].edge_start2 << ", " << axes[i].cert.contacts[2].edge_finish2 << ", "
                  << axes[i].cert.contacts[2].mix << ", " << axes[i].cert.contacts[2].vertex << "}\n";
        break;
      }
    }
  }

  std::cout << "Total passing: " << num_pass << "\n";
  return 0;
}
