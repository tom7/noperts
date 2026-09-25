#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static bool Barycentric4(const BigVecQ3 pts[4], const BigVecQ3 &target, BigRat lam[4]) {
  BigVecQ3 v0 = pts[0] - pts[3];
  BigVecQ3 v1 = pts[1] - pts[3];
  BigVecQ3 v2 = pts[2] - pts[3];
  BigVecQ3 w = target - pts[3];
  BigRat den = BigVecQ3::Det(v0, v1, v2);
  if (den == 0) return false;
  lam[0] = BigVecQ3::Det(w, v1, v2) / den;
  lam[1] = BigVecQ3::Det(v0, w, v2) / den;
  lam[2] = BigVecQ3::Det(v0, v1, w) / den;
  lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
  return true;
}

int main() {
  std::string file = ".artifacts/nopert229/tree_0_complete.json";
  auto root = LoadTreeJson(file, false, ".artifacts/nopert229");
  TreeNode *target = nullptr;
  auto find = [&](auto &self, TreeNode *node) -> void {
    if (node->path == "03121300") { target = node; return; }
    for (auto &c : node->children) self(self, c.get());
  };
  find(find, root.get());
  const auto &dec = *target->decomposed_cert;

  ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(target->GetTriangle(), c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));

  BigVecQ3 u[4];
  u[0] = ctr_ann / ax_ann.B;

  for (int a = 0; a < 3; a++) {
    ContactInfo ct[3] = {dec.complement_axes[a].contacts[0], dec.complement_axes[a].contacts[1], dec.complement_axes[a].contacts[2]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    Tube229::AuditAxis(target->GetTriangle(), ct, &ax, &ctr, &del, &err, BigRat(0));
    u[a + 1] = ctr / ax.B;
  }

  BigRat c_cone(5, 1000); // 0.005
  BigRat c_plus_delta(15, 10000); // 0.0015

  BigVecQ3 v[4];
  v[0] = u[0] * (c_plus_delta / c_cone);
  v[1] = u[1];
  v[2] = u[2];
  v[3] = u[3];

  BigRat target_scale = c_plus_delta * BigRat(7, 4);
  BigRat z0(0);
  BigVecQ3 targets[6] = {
    BigVecQ3(target_scale, z0, z0),
    BigVecQ3(-target_scale, z0, z0),
    BigVecQ3(z0, target_scale, z0),
    BigVecQ3(z0, -target_scale, z0),
    BigVecQ3(z0, z0, target_scale),
    BigVecQ3(z0, z0, -target_scale)
  };

  for (int k = 0; k < 6; k++) {
    BigRat lam[4];
    bool ok = Barycentric4(v, targets[k], lam);
    std::cout << "Target " << k << ": ok=" << ok
              << ", lam=[" << lam[0].ToDouble() << ", "
              << lam[1].ToDouble() << ", "
              << lam[2].ToDouble() << ", "
              << lam[3].ToDouble() << "]\n";
  }

  return 0;
}
