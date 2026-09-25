#include <iostream>
#include <vector>
#include <cmath>
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
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.z.ToDouble() / ax0.B.ToDouble()});
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.z.ToDouble() / ax0.B.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.027;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  double min_dot = 1e9;
  double min_phi = -1;
  int min_axis = -1;

  for (int step = 0; step < 3600; step++) {
    double phi = step * 2.0 * M_PI / 3600.0;
    vec3 p = yocto::normalize(std::cos(alpha) * u0 + std::sin(alpha) * (std::cos(phi) * ex + std::sin(phi) * ey));
    double max_d = -1e9;
    int best_a = -1;
    for (size_t a = 0; a < axes.size(); a++) {
      vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
      double d = yocto::dot(p, v);
      if (d > max_d) { max_d = d; best_a = a; }
    }
    if (max_d < min_dot) {
      min_dot = max_d;
      min_phi = phi * 180.0 / M_PI;
      min_axis = best_a;
    }
  }

  std::cout << "Circle psi = alpha (" << alpha * 180.0 / M_PI << " deg):\n";
  std::cout << "  Min max_dot over 3600 samples: " << min_dot << " at phi = " << min_phi << " deg (axis " << min_axis << ")\n";

  // Now test different polygon sizes N:
  for (int N : {20, 24, 30, 36, 40, 48, 60}) {
    double tan_outer = std::tan(alpha) / std::cos(M_PI / N);
    double psi_outer = std::atan(tan_outer);
    int fail_quads = 0;
    for (int k = 0; k < N; k++) {
      double phi1 = k * 2.0 * M_PI / N;
      double phi2 = (k + 1) * 2.0 * M_PI / N;
      vec3 A = yocto::normalize(std::cos(0.5 * psi_outer) * u0 + std::sin(0.5 * psi_outer) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
      vec3 B = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
      vec3 C = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi2) * ex + std::sin(phi2) * ey));
      vec3 D = yocto::normalize(std::cos(0.5 * psi_outer) * u0 + std::sin(0.5 * psi_outer) * (std::cos(phi2) * ex + std::sin(phi2) * ey));

      auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
        for (size_t a = 0; a < axes.size(); a++) {
          vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                        axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                        axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
          if (yocto::dot(p1, v) >= 0.0003 && yocto::dot(p2, v) >= 0.0003 && yocto::dot(p3, v) >= 0.0003) {
            return (int)a;
          }
        }
        return -1;
      };
      bool d1 = (check_tri(A, B, C) >= 0 && check_tri(A, C, D) >= 0);
      bool d2 = (check_tri(B, C, D) >= 0 && check_tri(B, D, A) >= 0);
      if (!d1 && !d2) fail_quads++;
    }
    std::cout << "N = " << N << " (psi_outer = " << psi_outer * 180 / M_PI << " deg): fail_quads = " << fail_quads << "\n";
  }

  return 0;
}
