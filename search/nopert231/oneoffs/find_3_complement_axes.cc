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
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Hull support pool: " << base_axes.size() << " axes\n";

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));

  BigRat c_cone("133/10000"); // 0.0133
  BigRat delta("13/10000");   // 0.0013
  BigRat c("18/10000");       // 0.0018

  BigRat v0_scale = (c + delta) / c_cone;
  BigVecQ3 v0 = ctr_ann * v0_scale;

  BigRat target_scale = (c + delta) * BigRat(7, 4);
  BigRat z0(0);
  BigVecQ3 targets[6] = {
    BigVecQ3(target_scale, z0, z0),
    BigVecQ3(-target_scale, z0, z0),
    BigVecQ3(z0, target_scale, z0),
    BigVecQ3(z0, -target_scale, z0),
    BigVecQ3(z0, z0, target_scale),
    BigVecQ3(z0, z0, -target_scale)
  };

  std::cout << "v0 = (" << v0.x.ToDouble() << ", " << v0.y.ToDouble() << ", " << v0.z.ToDouble() << ")\n";
  std::cout << "target_scale = " << target_scale.ToDouble() << "\n";

  // Filter candidate axes by delta <= delta
  std::vector<size_t> candidates;
  for (size_t i = 0; i < base_axes.size(); i++) {
    if (base_axes[i].delta <= delta) {
      candidates.push_back(i);
    }
  }
  std::cout << "Candidates with delta <= " << delta.ToDouble() << ": " << candidates.size() << "\n";

  // Check combinations
  for (size_t i1 : candidates) {
    const auto &ax1 = base_axes[i1];
    if (ax1.center.z >= 0) continue; // Need negative z

    for (size_t i2 : candidates) {
      if (i2 == i1) continue;
      const auto &ax2 = base_axes[i2];
      if (ax2.center.x <= 0) continue; // Need positive x

      for (size_t i3 : candidates) {
        if (i3 == i1 || i3 == i2) continue;
        const auto &ax3 = base_axes[i3];
        if (ax3.center.y <= 0) continue; // Need positive y

        BigVecQ3 pts[4] = {v0, ax1.center, ax2.center, ax3.center};
        bool all_in = true;
        for (int k = 0; k < 6; k++) {
          BigRat lam[4];
          if (!Barycentric4(pts, targets[k], lam)) {
            all_in = false; break;
          }
          if (lam[0] < 0 || lam[1] < 0 || lam[2] < 0 || lam[3] < 0) {
            all_in = false; break;
          }
        }

        if (all_in) {
          std::cout << "FOUND EXACT WINNING CAGE!\n";
          std::cout << "i1 = " << i1 << ", i2 = " << i2 << ", i3 = " << i3 << "\n";
          std::cout << "ax1 center = (" << ax1.center.x.ToDouble() << ", " << ax1.center.y.ToDouble() << ", " << ax1.center.z.ToDouble() << ")\n";
          std::cout << "ax2 center = (" << ax2.center.x.ToDouble() << ", " << ax2.center.y.ToDouble() << ", " << ax2.center.z.ToDouble() << ")\n";
          std::cout << "ax3 center = (" << ax3.center.x.ToDouble() << ", " << ax3.center.y.ToDouble() << ", " << ax3.center.z.ToDouble() << ")\n";
          return 0;
        }
      }
    }
  }

  std::cout << "No exact cage found with current directional filters.\n";
  return 1;
}
