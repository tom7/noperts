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
  vec3 u; // center / B
  vec3 dir; // normalized direction
};

static bool SolveTetraOrigin(const vec3& p0, const vec3& p1,
                             const vec3& p2, const vec3& p3,
                             double w[4]) {
  double M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  double rhs[3] = {-p3.x, -p3.y, -p3.z};

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

  int N = 200;
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
        vec3 dir = yocto::normalize(u);
        cands.push_back({{contacts[0], contacts[1], contacts[2]}, cert, center, delta, u, dir});
      }
    }
  }

  std::cout << "Audited " << cands.size() << " zero-defect axes.\n";

  // Filter to well-separated axes (1.5 degrees apart):
  std::vector<Cand> filtered;
  for (const auto& c : cands) {
    bool keep = true;
    for (const auto& f : filtered) {
      if (yocto::dot(c.dir, f.dir) > std::cos(1.5 * M_PI / 180.0)) {
        keep = false;
        break;
      }
    }
    if (keep) filtered.push_back(c);
  }
  std::cout << "Filtered to " << filtered.size() << " axes.\n";

  // For each candidate i0, find the most opposing axis i1:
  std::cout << "Searching for strictly positive 4-axis cage...\n";
  double best_min_w = -1.0;

  for (size_t i0 = 0; i0 < filtered.size(); i0++) {
    // Find top 10 most opposing axes to i0:
    std::vector<std::pair<double, size_t>> opposing;
    for (size_t i = 0; i < filtered.size(); i++) {
      if (i == i0) continue;
      double d = yocto::dot(filtered[i0].dir, filtered[i].dir);
      if (d < -0.8) {
        opposing.push_back({d, i});
      }
    }
    std::sort(opposing.begin(), opposing.end());

    for (size_t k1 = 0; k1 < std::min((size_t)8, opposing.size()); k1++) {
      size_t i1 = opposing[k1].second;
      // Normal of the opposing line i0 - i1:
      vec3 line_dir = filtered[i0].dir;

      // Find candidates that are roughly transverse to the line:
      std::vector<size_t> transverse;
      for (size_t i = 0; i < filtered.size(); i++) {
        if (i == i0 || i == i1) continue;
        double dot_val = std::abs(yocto::dot(line_dir, filtered[i].dir));
        if (dot_val < 0.7) {
          transverse.push_back(i);
        }
      }

      // Check pairs in transverse:
      for (size_t a = 0; a < transverse.size(); a++) {
        size_t i2 = transverse[a];
        for (size_t b = a + 1; b < transverse.size(); b++) {
          size_t i3 = transverse[b];

          double w[4];
          if (SolveTetraOrigin(filtered[i0].u, filtered[i1].u,
                               filtered[i2].u, filtered[i3].u, w)) {
            double min_w = std::min({w[0], w[1], w[2], w[3]});
            if (min_w > best_min_w) {
              best_min_w = min_w;
              std::cout << "Found better cage! min_w = " << best_min_w
                        << " (w0=" << w[0] << ", w1=" << w[1] << ", w2=" << w[2] << ", w3=" << w[3] << ")\n";
              if (best_min_w > 0.001) {
                std::cout << "\n=========================================\n";
                std::cout << "SUCCESS! FOUND STRICTLY POSITIVE CAGE WITH > 0.1% MARGIN!\n";
                std::cout << "Indices: " << i0 << ", " << i1 << ", " << i2 << ", " << i3 << "\n";
                std::cout << "=========================================\n";
                return 0;
              }
            }
          }
        }
      }
    }
  }

  std::cout << "Search complete. Best min_w = " << best_min_w << "\n";
  return 0;
}
