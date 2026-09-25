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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  // Annular axis u0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(1, 1000))) {
    std::cerr << "ax0 failed\n";
    return 1;
  }
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "Collecting audited axes across viewpoints...\n";
  int N = 300;
  std::vector<Tube229::AuditedAxis> all_audited;

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

  std::cout << "Total audited axes: " << all_audited.size() << "\n";

  // Deduplicate/cluster by direction to get diverse axes:
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
      if (yocto::dot(unorm, other / yocto::length(other)) > 0.99) {
        too_close = true;
        break;
      }
    }
    if (!too_close) {
      diverse.push_back(ax);
      u_diverse.push_back(u);
    }
  }

  std::cout << "Filtered to " << diverse.size() << " spatially diverse axes!\n";

  double delta = 0.000234013;
  double box_c = 0.001;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  for (double c_cone : {0.05, 0.045, 0.04, 0.035, 0.03, 0.025}) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;

    double best_min_l = -1e9;
    int best_i = -1, best_j = -1, best_k = -1;

    int M = u_diverse.size();
    for (int i = 0; i < M; i++) {
      vec3 v1 = u_diverse[i];
      for (int j = i + 1; j < M; j++) {
        vec3 v2 = u_diverse[j];
        for (int k = j + 1; k < M; k++) {
          vec3 v3 = u_diverse[k];

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
          }

          if (min_l > best_min_l) {
            best_min_l = min_l;
            best_i = i; best_j = j; best_k = k;
          }
        }
      }
    }

    std::cout << "c_cone = " << c_cone << ": best_min_l = " << best_min_l
              << " with axes (" << best_i << ", " << best_j << ", " << best_k << ")\n";
    if (best_min_l > 0) {
      std::cout << "SUCCESS! FOUND VALID CAGE FOR c_cone = " << c_cone << "!\n";
      // Print contacts of the winning axes:
      int winning[3] = {best_i, best_j, best_k};
      for (int w = 0; w < 3; w++) {
        std::cout << "Axis " << (w + 1) << " (idx " << winning[w] << "): \n";
        for (int m = 0; m < 3; m++) {
          const auto &c = diverse[winning[w]].cert.contacts[m];
          std::cout << "  MakeContact(" << c.edge_start << ", " << c.edge_finish
                    << ", " << c.edge_start2 << ", " << c.edge_finish2
                    << ", " << c.mix << ", " << c.vertex << "),\n";
        }
      }
      break;
    }
  }

  return 0;
}
