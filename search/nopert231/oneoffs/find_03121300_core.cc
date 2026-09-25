#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  TriangleQ tri = TriangleFromPath("0312130332");

  ContactInfo c_ann[3] = {
    { .edge_start = 3, .edge_finish = 2, .edge_start2 = 2, .edge_finish2 = 1, .mix = 800, .vertex = 2 },
    { .edge_start = 1, .edge_finish = 4, .edge_start2 = 4, .edge_finish2 = 8, .mix = 800, .vertex = 4 },
    { .edge_start = 13, .edge_finish = 14, .edge_start2 = 14, .edge_finish2 = 15, .mix = 200, .vertex = 14 }
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000"));

  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);
  std::cout << "u0: " << u0.x << ", " << u0.y << ", " << u0.z << "\n";
  std::cout << "u0_dir: " << u0_dir.x << ", " << u0_dir.y << ", " << u0_dir.z << "\n";

  // Let's search pure vertex contacts or pure edge endpoints (mix=0 or mix=1000)
  // or any contacts that give zero defect (supportUpper <= 0).
  // Tube229::GenerateCandidatesForView with try_mix=false generates pure vertex contacts!
  std::vector<vec3> test_dirs;
  test_dirs.push_back(u0_dir);
  for (double dtheta = 0.01; dtheta <= 0.1; dtheta += 0.01) {
    for (double phi = 0; phi < 2 * M_PI; phi += 0.2) {
      vec3 perp1 = yocto::normalize(yocto::cross(u0_dir, vec3{0, 1, 0}));
      vec3 perp2 = yocto::cross(u0_dir, perp1);
      vec3 v = yocto::normalize(u0_dir * std::cos(dtheta) + (perp1 * std::cos(phi) + perp2 * std::sin(phi)) * std::sin(dtheta));
      test_dirs.push_back(v);
    }
  }

  std::cout << "Searching over " << test_dirs.size() << " directions for pure vertex/zero defect axis...\n";

  double best_angle = 1e9;
  AxisCertificate best_ax;
  BigVecQ3 best_ctr;
  BigRat best_del;

  for (const auto &v : test_dirs) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, false, 5, false);
    for (const auto &cand : cands) {
      ContactInfo test_c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate ax;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
        // Zero defect! Check delta <= 1/1000
        vec3 u = {ctr.x.ToDouble() / ax.B.ToDouble(),
                  ctr.y.ToDouble() / ax.B.ToDouble(),
                  ctr.z.ToDouble() / ax.B.ToDouble()};
        double dot = yocto::dot(yocto::normalize(u), u0_dir);
        if (dot > 0.9) {
          double angle = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
          if (angle < best_angle) {
            best_angle = angle;
            best_ax = ax;
            best_ctr = ctr;
            best_del = del;
            std::cout << "Found zero-defect axis: angle = " << angle << " deg, B = " << ax.B.ToDouble() << ", del = " << del.ToDouble() << "\n";
          }
        }
      }
    }
  }

  std::cout << "Best angle: " << best_angle << " deg\n";
  return 0;
}
