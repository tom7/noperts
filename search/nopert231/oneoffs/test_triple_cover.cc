#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto all_axes = Tube229::FindAllHullSupportAxes(tri, 100);
  std::vector<vec3> cand_u;
  for (const auto &ax : all_axes) {
    cand_u.push_back(vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                          ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                          ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  double c_cone = 0.024;
  double target_c = 0.001;

  // Sample sphere outside cone:
  int N = 5000;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    if (yocto::dot(a, u0) < c_cone) {
      pts.push_back(a);
    }
  }

  int M = cand_u.size();
  std::cout << "Testing all triples of " << M << " axes against " << pts.size() << " points...\n";

  for (int i = 0; i < M; i++) {
    for (int j = i + 1; j < M; j++) {
      for (int k = j + 1; k < M; k++) {
        bool ok = true;
        for (const auto &p : pts) {
          if (yocto::dot(p, cand_u[i]) < target_c &&
              yocto::dot(p, cand_u[j]) < target_c &&
              yocto::dot(p, cand_u[k]) < target_c) {
            ok = false;
            break;
          }
        }
        if (ok) {
          std::cout << "FOUND TRIPLE THAT COVERS: (" << i << ", " << j << ", " << k << ")\n";
          return 0;
        }
      }
    }
  }

  std::cout << "No triple among " << M << " axes covers the complement.\n";
  return 0;
}
