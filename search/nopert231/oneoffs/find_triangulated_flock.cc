#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

struct Triangle3D {
  vec3 A, B, C;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);
  double norm_u0 = yocto::length(u0_raw);

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha); // ~69.2 deg
  double c_core = 0.0001;

  std::cout << "Cone half-angle alpha = " << alpha * 180.0 / M_PI << " deg\n";
  std::cout << "Target c_core = " << c_core << "\n";

  // Pre-extract all candidate axes:
  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  // We test triangulations with 1 center vertex and 1 or 2 concentric rings of vertices.
  // Ring 1 at angle psi1, Ring 2 at angle alpha (or slightly larger, alpha / cos(pi/N) so the spherical polygon circumscribes the circle!)
  // If a regular N-gon has side midpoints on the circle of angle alpha:
  // tan(psi_outer) = tan(alpha) / cos(pi/N)
  for (int N : {8, 12, 16, 20, 24, 32}) {
    double tan_alpha = std::tan(alpha);
    double tan_outer = tan_alpha / std::cos(M_PI / N);
    double psi_outer = std::atan(tan_outer);

    for (double psi_ratio : {0.4, 0.5, 0.6}) {
      double psi_inner = psi_ratio * psi_outer;

      std::vector<Triangle3D> tris;
      vec3 apex = u0;

      std::vector<vec3> ring1(N), ring2(N);
      for (int k = 0; k < N; k++) {
        double phi = k * 2.0 * M_PI / N;
        ring1[k] = yocto::normalize(std::cos(psi_inner) * u0 + std::sin(psi_inner) * (std::cos(phi) * ex + std::sin(phi) * ey));
        ring2[k] = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi) * ex + std::sin(phi) * ey));
      }

      for (int k = 0; k < N; k++) {
        int next_k = (k + 1) % N;
        // Inner triangle
        tris.push_back({apex, ring1[k], ring1[next_k]});
        // Outer quad split into 2 triangles
        tris.push_back({ring1[k], ring2[k], ring2[next_k]});
        tris.push_back({ring1[k], ring2[next_k], ring1[next_k]});
      }

      // For each triangle, can any axis in all_v cover all 3 vertices with margin >= c_core?
      std::vector<std::vector<int>> covering_axes(tris.size());
      bool all_covered = true;
      for (size_t t = 0; t < tris.size(); t++) {
        for (size_t i = 0; i < all_v.size(); i++) {
          if (yocto::dot(tris[t].A, all_v[i]) >= c_core &&
              yocto::dot(tris[t].B, all_v[i]) >= c_core &&
              yocto::dot(tris[t].C, all_v[i]) >= c_core) {
            covering_axes[t].push_back(i);
          }
        }
        if (covering_axes[t].empty()) {
          all_covered = false;
        }
      }

      if (all_covered) {
        // Find minimal set of axes to cover all tris using greedy set cover
        std::vector<bool> tri_cov(tris.size(), false);
        int n_cov = 0;
        std::vector<int> chosen;
        while (n_cov < (int)tris.size()) {
          int best_ax = -1, best_new = -1;
          for (size_t i = 0; i < all_v.size(); i++) {
            int n = 0;
            for (size_t t = 0; t < tris.size(); t++) {
              if (!tri_cov[t]) {
                for (int a : covering_axes[t]) {
                  if (a == (int)i) { n++; break; }
                }
              }
            }
            if (n > best_new) {
              best_new = n;
              best_ax = i;
            }
          }
          if (best_new <= 0) break;
          chosen.push_back(best_ax);
          for (size_t t = 0; t < tris.size(); t++) {
            if (!tri_cov[t]) {
              for (int a : covering_axes[t]) {
                if (a == best_ax) {
                  tri_cov[t] = true;
                  n_cov++;
                  break;
                }
              }
            }
          }
        }
        std::cout << "N = " << N << ", ratio = " << psi_ratio << ": SUCCESS! All "
                  << tris.size() << " triangles covered using " << chosen.size() << " axes!\n";
        std::cout << "  Chosen axes: ";
        for (int a : chosen) std::cout << a << " ";
        std::cout << "\n";
        return 0;
      }
    }
  }

  std::cout << "No clean triangulation found with 2 rings.\n";
  return 0;
}
