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

struct Cand {
  ContactInfo c[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 u;
};

static bool SolveTetraOrigin(const BigVecQ3& p0, const BigVecQ3& p1,
                             const BigVecQ3& p2, const BigVecQ3& p3,
                             BigRat w[4]) {
  BigRat M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  BigRat rhs[3] = {-p3.x, -p3.y, -p3.z};

  BigRat det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (det == BigRat(0)) return false;

  BigRat d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  BigRat d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  BigRat d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = BigRat(1) - w[0] - w[1] - w[2];
  return true;
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);
  std::string err;

  // Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 250, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 390, 15)
  };
  AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0))) {
    std::cout << "Axis 0 audit failed\n"; return 1;
  }
  BigVecQ3 u0_exact = cnt0 / ax0.B;
  vec3 u0 = {u0_exact.x.ToDouble(), u0_exact.y.ToDouble(), u0_exact.z.ToDouble()};
  vec3 T = yocto::normalize(-u0); // Target direction opposing Axis 0

  // Build orthonormal basis (ex, ey, T):
  vec3 up = {0, 0, 1};
  if (std::abs(yocto::dot(T, up)) > 0.9) up = {1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(up, T));
  vec3 ey = yocto::cross(T, ex);

  std::cout << "Target direction T opposing Axis 0: " << T.x << ", " << T.y << ", " << T.z << "\n";

  // Collect candidate zero-defect axes:
  std::cout << "Harvesting zero-defect axes in the forward hemisphere of T...\n";
  std::vector<Cand> fwd_cands;

  int N = 100;
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
        double z_proj = yocto::dot(u, T);
        if (z_proj > 0.001) { // Forward hemisphere of T
          fwd_cands.push_back({{contacts[0], contacts[1], contacts[2]}, cert, center, delta, u});
        }
      }
    }
  }

  std::cout << "Found " << fwd_cands.size() << " axes in forward hemisphere of T.\n";

  // Compute 2D coordinates:
  struct Pt2D {
    double x, y;
    size_t idx;
  };
  std::vector<Pt2D> pts;
  for (size_t i = 0; i < fwd_cands.size(); i++) {
    double z = yocto::dot(fwd_cands[i].u, T);
    double x = yocto::dot(fwd_cands[i].u, ex) / z;
    double y = yocto::dot(fwd_cands[i].u, ey) / z;
    pts.push_back({x, y, i});
  }

  // Find 3 points in pts that form a triangle enclosing (0,0):
  std::cout << "Searching for 2D triangles enclosing (0,0)...\n";
  double best_margin = -1.0;
  size_t best_i1 = 0, best_i2 = 0, best_i3 = 0;

  for (size_t i = 0; i < pts.size(); i++) {
    for (size_t j = i + 1; j < pts.size(); j++) {
      for (size_t k = j + 1; k < pts.size(); k++) {
        // 2D barycentric coordinates of (0,0):
        double x1 = pts[i].x, y1 = pts[i].y;
        double x2 = pts[j].x, y2 = pts[j].y;
        double x3 = pts[k].x, y3 = pts[k].y;

        double det = (y2 - y3)*(x1 - x3) + (x3 - x2)*(y1 - y3);
        if (std::abs(det) < 1e-9) continue;

        double w1 = ((y2 - y3)*(0 - x3) + (x3 - x2)*(0 - y3)) / det;
        double w2 = ((y3 - y1)*(0 - x3) + (x1 - x3)*(0 - y3)) / det;
        double w3 = 1.0 - w1 - w2;

        double min_w = std::min({w1, w2, w3});
        if (min_w > best_margin) {
          best_margin = min_w;
          best_i1 = pts[i].idx;
          best_i2 = pts[j].idx;
          best_i3 = pts[k].idx;
          std::cout << "New best 2D margin: " << best_margin << " (w1=" << w1
                    << ", w2=" << w2 << ", w3=" << w3 << ")\n";
        }
      }
    }
  }

  if (best_margin > 0.0) {
    std::cout << "\n============================================\n";
    std::cout << "SUCCESS! FOUND 2D TRIANGLE ENCLOSING (0,0) WITH MARGIN: " << best_margin << "\n";
    std::cout << "============================================\n";

    // Test exact 3D barycentric weights of the origin with Axis 0:
    BigVecQ3 u1_exact = fwd_cands[best_i1].center / fwd_cands[best_i1].cert.B;
    BigVecQ3 u2_exact = fwd_cands[best_i2].center / fwd_cands[best_i2].cert.B;
    BigVecQ3 u3_exact = fwd_cands[best_i3].center / fwd_cands[best_i3].cert.B;

    BigRat w[4];
    if (SolveTetraOrigin(u0_exact, u1_exact, u2_exact, u3_exact, w)) {
      std::cout << "Exact 3D weights of origin:\n";
      std::cout << "  w0 = " << w[0].ToString() << " (" << w[0].ToDouble() << ")\n";
      std::cout << "  w1 = " << w[1].ToString() << " (" << w[1].ToDouble() << ")\n";
      std::cout << "  w2 = " << w[2].ToString() << " (" << w[2].ToDouble() << ")\n";
      std::cout << "  w3 = " << w[3].ToString() << " (" << w[3].ToDouble() << ")\n";

      if (w[0] > BigRat(0) && w[1] > BigRat(0) && w[2] > BigRat(0) && w[3] > BigRat(0)) {
        std::cout << "CONFIRMED: ALL 4 3D WEIGHTS ARE STRICTLY POSITIVE!\n";
      }
    }
  } else {
    std::cout << "Best margin <= 0: " << best_margin << "\n";
  }

  return 0;
}
