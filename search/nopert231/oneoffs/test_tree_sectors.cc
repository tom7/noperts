#include <iostream>
#include <vector>
#include <cmath>
#include <set>
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

  double c_cone = 0.020;
  double c_core = 0.0005;

  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
    for (size_t a = 0; a < axes.size(); a++) {
      vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
      if (yocto::dot(p1, v) >= c_core * yocto::length(p1) &&
          yocto::dot(p2, v) >= c_core * yocto::length(p2) &&
          yocto::dot(p3, v) >= c_core * yocto::length(p3)) {
        return (int)a;
      }
    }
    return -1;
  };

  for (int N : {4, 6, 8, 10, 12}) {
    double tan_outer = std::tan(alpha) / std::cos(M_PI / N);
    double R = tan_outer / norm_u0;
    vec3 P0 = u0 / norm_u0; // in plane <x, u0_unnorm> = 1

    int leaf_count = 0;
    std::set<int> used_axes;

    auto subdivide = [&](auto& self, vec3 p1, vec3 p2, vec3 p3, int depth) -> bool {
      int a = check_tri(p1, p2, p3);
      if (a >= 0) {
        leaf_count++;
        used_axes.insert(a);
        return true;
      }
      if (depth >= 10) {
        std::cout << "Failed tri at depth " << depth << ":\n"
                  << "  p1=(" << p1.x << ", " << p1.y << ", " << p1.z << ")\n"
                  << "  p2=(" << p2.x << ", " << p2.y << ", " << p2.z << ")\n"
                  << "  p3=(" << p3.x << ", " << p3.y << ", " << p3.z << ")\n";
        return false;
      }
      vec3 m12 = (p1 + p2) * 0.5;
      vec3 m23 = (p2 + p3) * 0.5;
      vec3 m31 = (p3 + p1) * 0.5;
      return self(self, p1, m12, m31, depth + 1) &&
             self(self, m12, p2, m23, depth + 1) &&
             self(self, m31, m23, p3, depth + 1) &&
             self(self, m23, m31, m12, depth + 1);
    };

    bool all_ok = true;
    for (int k = 0; k < N; k++) {
      double phi1 = k * 2.0 * M_PI / N;
      double phi2 = (k + 1) * 2.0 * M_PI / N;
      vec3 V1 = P0 + R * (std::cos(phi1) * ex + std::sin(phi1) * ey);
      vec3 V2 = P0 + R * (std::cos(phi2) * ex + std::sin(phi2) * ey);
      if (!subdivide(subdivide, P0, V1, V2, 0)) {
        std::cout << "N=" << N << " failed at sector " << k << "\n";
        all_ok = false;
        break;
      }
    }

    std::cout << "N=" << N << ": all_ok=" << all_ok
              << ", leaf_count=" << leaf_count
              << ", used_axes=" << used_axes.size() << "\n";
  }

  return 0;
}
