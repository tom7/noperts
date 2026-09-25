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

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));
  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  std::cout << "Target u0_dir: (" << u0_dir.x << ", " << u0_dir.y << ", " << u0_dir.z << ")\n";

  // Search a grid of directions within 40 degrees of u0_dir:
  double min_ang = 1e9;
  ContactInfo best_c[3];
  AxisCertificate best_ax;
  BigVecQ3 best_ctr;
  BigRat best_del;

  // Generate candidates around u0_dir with various small cone angles:
  for (double alpha = 0.0; alpha <= 0.7; alpha += 0.05) {
    for (double phi = 0; phi < 2 * M_PI; phi += 0.2) {
      vec3 perp1 = yocto::normalize(yocto::cross(u0_dir, vec3{0, 1, 0}));
      vec3 perp2 = yocto::cross(u0_dir, perp1);
      vec3 dir = yocto::normalize(u0_dir * std::cos(alpha) + (perp1 * std::cos(phi) + perp2 * std::sin(phi)) * std::sin(alpha));

      // candidate generation with try_mix = true:
      // Remember: include_boundaries = true!
      auto cands = Tube229::GenerateCandidatesForView(dir, tri, true, 4, true);
      for (const auto &cand : cands) {
        ContactInfo test_c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
        AxisCertificate ax;
        BigVecQ3 ctr;
        BigRat del;
        if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
          vec3 v = {ctr.x.ToDouble() / ax.B.ToDouble(),
                    ctr.y.ToDouble() / ax.B.ToDouble(),
                    ctr.z.ToDouble() / ax.B.ToDouble()};
          double dot = yocto::dot(u0_dir, yocto::normalize(v));
          if (dot > 0.5) { // positive hemisphere!
            double ang = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
            if (ang < min_ang) {
              min_ang = ang;
              best_c[0] = test_c[0]; best_c[1] = test_c[1]; best_c[2] = test_c[2];
              best_ax = ax;
              best_ctr = ctr;
              best_del = del;
              std::cout << "Found aligned zero-defect axis: angle = " << ang << " deg, del = " << del.ToDouble() << "\n";
              for (int m = 0; m < 3; m++) {
                std::cout << "  c[" << m << "]: start=" << test_c[m].edge_start << ", finish=" << test_c[m].edge_finish
                          << ", mix=" << test_c[m].mix << ", v=" << test_c[m].vertex << "\n";
              }
            }
          }
        }
      }
    }
  }

  std::cout << "\nBest positive-hemisphere zero-defect axis angle: " << min_ang << " deg\n";
  return 0;
}
