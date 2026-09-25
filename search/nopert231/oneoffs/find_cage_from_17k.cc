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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "Collecting audited axes across viewpoints...\n";
  int N = 200;
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

  // Deduplicate/cluster by direction to get ~300 diverse axes:
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
      if (yocto::dot(unorm, other / yocto::length(other)) > 0.995) {
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

  // Now test triples with c_cone = 0.028:
  double delta = 3.33e-7;
  double c_cone = 0.028;
  double box_c = 1e-7;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct_dirs = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  int M = diverse.size();
  double best_min_l = -1e9;
  int bi = -1, bj = -1, bk = -1;

  for (int i = 0; i < M; i++) {
    vec3 d1 = u_diverse[i] - v0;
    for (int j = i + 1; j < M; j++) {
      vec3 d2 = u_diverse[j] - v0;
      vec3 c12 = yocto::cross(d1, d2);
      if (yocto::length(c12) < 1e-6) continue;

      for (int k = j + 1; k < M; k++) {
        vec3 d3 = u_diverse[k] - v0;
        double det = yocto::dot(c12, d3);
        if (std::abs(det) < 1e-8) continue;

        vec3 c23 = yocto::cross(d2, d3);
        vec3 c31 = yocto::cross(d3, d1);

        double min_l = 1e9;
        for (int m = 0; m < 6; m++) {
          vec3 dp = oct_dirs[m] * R - v0;
          double l1 = yocto::dot(dp, c23) / det;
          double l2 = yocto::dot(dp, c31) / det;
          double l3 = yocto::dot(dp, c12) / det;
          double l0 = 1.0 - l1 - l2 - l3;
          double min_vert = std::min({l0, l1, l2, l3});
          if (min_vert < min_l) min_l = min_vert;
          if (min_l <= best_min_l) break;
        }

        if (min_l > best_min_l) {
          best_min_l = min_l;
          bi = i; bj = j; bk = k;
          std::cout << "New best min_l: " << best_min_l << " with ("
                    << bi << ", " << bj << ", " << bk << ")\n";
          if (best_min_l > 0) {
            std::cout << "SUCCESS! Strictly positive cage found!\n";
            std::cout << "Axis 1 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  v=" << diverse[bi].cert.contacts[c].vertex
                        << " mix=" << diverse[bi].cert.contacts[c].mix
                        << " e1=" << diverse[bi].cert.contacts[c].edge_start << "->" << diverse[bi].cert.contacts[c].edge_finish
                        << " e2=" << diverse[bi].cert.contacts[c].edge_start2 << "->" << diverse[bi].cert.contacts[c].edge_finish2 << "\n";
            }
            std::cout << "Axis 2 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  v=" << diverse[bj].cert.contacts[c].vertex
                        << " mix=" << diverse[bj].cert.contacts[c].mix
                        << " e1=" << diverse[bj].cert.contacts[c].edge_start << "->" << diverse[bj].cert.contacts[c].edge_finish
                        << " e2=" << diverse[bj].cert.contacts[c].edge_start2 << "->" << diverse[bj].cert.contacts[c].edge_finish2 << "\n";
            }
            std::cout << "Axis 3 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  v=" << diverse[bk].cert.contacts[c].vertex
                        << " mix=" << diverse[bk].cert.contacts[c].mix
                        << " e1=" << diverse[bk].cert.contacts[c].edge_start << "->" << diverse[bk].cert.contacts[c].edge_finish
                        << " e2=" << diverse[bk].cert.contacts[c].edge_start2 << "->" << diverse[bk].cert.contacts[c].edge_finish2 << "\n";
            }
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Overall best min_l: " << best_min_l << "\n";
  return 0;
}
