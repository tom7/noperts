#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  std::cout << "Collecting audited axes across viewpoints...\n";
  int N = 200;
  std::vector<Tube229::AuditedAxis> all_audited;
  std::string err;

  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : cands) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        all_audited.push_back({cert, center, delta});
      }
    }
  }

  std::vector<Tube229::AuditedAxis> diverse;
  std::vector<vec3> u_diverse;
  for (const auto &ax : all_audited) {
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    double ulen = yocto::length(u);
    if (ulen < 1e-6) continue;
    vec3 unorm = u / ulen;
    bool too_close = false;
    for (const auto &other : u_diverse) {
      if (yocto::dot(unorm, other / yocto::length(other)) > 0.95) {
        too_close = true;
        break;
      }
    }
    if (!too_close) {
      diverse.push_back(ax);
      u_diverse.push_back(u);
    }
  }

  std::cout << "Diverse axes: " << u_diverse.size() << "\n";

  double delta = 0.000234013;
  double box_c = 0.001;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  int M = u_diverse.size();
  std::cout << "Testing quadruples of zero-defect axes...\n";
  double best_min_l = -1e9;
  int b0 = -1, b1 = -1, b2 = -1, b3 = -1;

  for (int i0 = 0; i0 < M; i0++) {
    vec3 v0 = u_diverse[i0];
    for (int i1 = i0 + 1; i1 < M; i1++) {
      vec3 v1 = u_diverse[i1];
      for (int i2 = i1 + 1; i2 < M; i2++) {
        vec3 v2 = u_diverse[i2];
        for (int i3 = i2 + 1; i3 < M; i3++) {
          vec3 v3 = u_diverse[i3];

          vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
          double det = yocto::dot(d1, yocto::cross(d2, d3));
          if (std::abs(det) < 1e-9) continue;
          vec3 c23 = yocto::cross(d2, d3);

          double min_l = 1e9;
          for (const auto &p : oct) {
            vec3 dp = p - v0;
            double l1 = yocto::dot(dp, c23) / det;
            double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
            double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
            double l0 = 1.0 - l1 - l2 - l3;
            min_l = std::min({min_l, l0, l1, l2, l3});
            if (min_l <= 0) break;
          }

          if (min_l > best_min_l) {
            best_min_l = min_l;
            b0 = i0; b1 = i1; b2 = i2; b3 = i3;
            std::cout << "New best pure zero-defect cage: min_l = " << min_l
                      << " (" << b0 << ", " << b1 << ", " << b2 << ", " << b3 << ")\n";
            if (min_l > 0) {
              std::cout << "FOUND PURE ZERO-DEFECT 4-AXIS CAGE!\n";
              return 0;
            }
          }
        }
      }
    }
  }

  std::cout << "Finished. Best min_l = " << best_min_l << "\n";
  return 0;
}
