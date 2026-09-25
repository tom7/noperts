#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

struct Cand {
  ContactInfo c[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 u;
};

static bool SolveTetraPoint(const vec3& p0, const vec3& p1,
                            const vec3& p2, const vec3& p3,
                            const vec3& target,
                            double w[4]) {
  double M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  double rhs[3] = {target.x - p3.x, target.y - p3.y, target.z - p3.z};

  double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (std::abs(det) < 1e-12) return false;

  double d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  double d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  double d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = 1.0 - w[0] - w[1] - w[2];
  return true;
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  std::cout << "Collecting zero-defect axes...\n";
  std::vector<Cand> cands;
  std::string err;

  int N = 150;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto candidates = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : candidates) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        vec3 u = {center.x.ToDouble() / cert.B.ToDouble(),
                  center.y.ToDouble() / cert.B.ToDouble(),
                  center.z.ToDouble() / cert.B.ToDouble()};
        cands.push_back({{contacts[0], contacts[1], contacts[2]}, cert, center, delta, u});
      }
    }
  }

  std::cout << "Audited " << cands.size() << " zero-defect axes.\n";

  // Filter down to unique, well-separated axes (at least 2.5 degrees apart):
  std::vector<Cand> filtered;
  for (const auto& c : cands) {
    bool keep = true;
    for (const auto& f : filtered) {
      if (yocto::dot(c.u, f.u) / (yocto::length(c.u) * yocto::length(f.u)) > std::cos(2.5 * M_PI / 180.0)) {
        keep = false;
        break;
      }
    }
    if (keep) filtered.push_back(c);
  }
  std::cout << "Filtered to " << filtered.size() << " well-separated axes.\n";

  // Octahedron scale:
  double c_cone = 0.025;
  double c_val = 0.00041;
  double delta_val = 0.00024;
  double contracted_scale = (c_val + delta_val) / c_cone;
  double oct_radius = (7.0 / 4.0) * (c_val + delta_val);

  vec3 oct_pts[6] = {
    { oct_radius, 0, 0 },
    {-oct_radius, 0, 0 },
    { 0,  oct_radius, 0 },
    { 0, -oct_radius, 0 },
    { 0, 0,  oct_radius },
    { 0, 0, -oct_radius }
  };

  std::cout << "Searching for a 4-axis cage where contracted p0, p1, p2, p3 cage all 6 octahedron vertices...\n";

  for (size_t i0 = 0; i0 < filtered.size(); i0++) {
    vec3 p0 = yocto::normalize(filtered[i0].u) * contracted_scale;
    std::vector<size_t> opp;
    for (size_t i = 0; i < filtered.size(); i++) {
      if (yocto::dot(filtered[i0].u, filtered[i].u) < -0.1) {
        opp.push_back(i);
      }
    }
    if (opp.size() < 3) continue;

    for (size_t a = 0; a < opp.size(); a++) {
      size_t i1 = opp[a];
      vec3 p1 = yocto::normalize(filtered[i1].u);
      for (size_t b = a + 1; b < opp.size(); b++) {
        size_t i2 = opp[b];
        vec3 p2 = yocto::normalize(filtered[i2].u);
        for (size_t c = b + 1; c < opp.size(); c++) {
          size_t i3 = opp[c];
          vec3 p3 = yocto::normalize(filtered[i3].u);

          bool all_in = true;
          double min_w_all = 1.0;
          for (int k = 0; k < 6; k++) {
            double w[4];
            if (!SolveTetraPoint(p0, p1, p2, p3, oct_pts[k], w)) {
              all_in = false; break;
            }
            double min_w = std::min({w[0], w[1], w[2], w[3]});
            if (min_w <= 0.01) {
              all_in = false; break;
            }
            if (min_w < min_w_all) min_w_all = min_w;
          }

          if (all_in) {
            std::cout << "SUCCESS! Found valid decomposed cage!\n";
            std::cout << "  i0=" << i0 << " i1=" << i1 << " i2=" << i2 << " i3=" << i3 << "\n";
            std::cout << "  min_w_all = " << min_w_all << "\n";
            for (int ax_idx : {(int)i0, (int)i1, (int)i2, (int)i3}) {
              std::cout << "  Axis " << ax_idx << ":\n";
              std::cout << "    B = " << filtered[ax_idx].cert.B.ToString() << "\n";
              std::cout << "    contacts:\n";
              for (int m = 0; m < 3; m++) {
                const auto& ci = filtered[ax_idx].c[m];
                std::cout << "      MakeContact(" << ci.edge_start << ", " << ci.edge_finish
                          << ", " << ci.edge_start2 << ", " << ci.edge_finish2 << ", "
                          << ci.mix << ", " << ci.vertex << ")\n";
              }
              std::cout << "    nonzeroWitness: [" << filtered[ax_idx].cert.nonzero_witness[0]
                        << ", " << filtered[ax_idx].cert.nonzero_witness[1]
                        << ", " << filtered[ax_idx].cert.nonzero_witness[2] << "]\n";
            }
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Search complete, no cage found with current parameters.\n";
  return 0;
}
