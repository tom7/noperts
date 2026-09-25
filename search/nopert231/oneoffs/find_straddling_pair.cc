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

static bool SolveTetraOriginDouble(const vec3& p0, const vec3& p1,
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

struct AxisCand {
  ContactInfo c[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  BigVecQ3 u_exact;
  vec3 u;
  double theta; // Transverse angle
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Zero-defect Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 400, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 390, 15)
  };
  AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0))) {
    std::cout << "Axis 0 audit failed\n"; return 1;
  }
  BigVecQ3 u0_exact = cnt0 / ax0.B;
  vec3 u0 = {u0_exact.x.ToDouble(), u0_exact.y.ToDouble(), u0_exact.z.ToDouble()};

  // Zero-defect Axis 1:
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 700, 15),
    MakeContact(19, 3, 3, 2, 750, 3)
  };
  AxisCertificate ax1; BigVecQ3 cnt1; BigRat del1;
  if (!Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &del1, &err, BigRat(0))) {
    std::cout << "Axis 1 audit failed\n"; return 1;
  }
  BigVecQ3 u1_exact = cnt1 / ax1.B;
  vec3 u1 = {u1_exact.x.ToDouble(), u1_exact.y.ToDouble(), u1_exact.z.ToDouble()};

  // Build coordinate frame with n along u0:
  vec3 n = yocto::normalize(u0);
  vec3 up = {0, 0, 1};
  if (std::abs(yocto::dot(n, up)) > 0.9) up = {1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(up, n));
  vec3 ey = yocto::cross(n, ex);

  // Harvesting candidates:
  std::cout << "Harvesting zero-defect candidate axes...\n";
  std::vector<AxisCand> pool;

  int N = 80;
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
        BigVecQ3 u_ex = center / cert.B;
        vec3 u_vec = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
        double px = yocto::dot(u_vec, ex);
        double py = yocto::dot(u_vec, ey);
        double trans_len = std::hypot(px, py);
        if (trans_len > 0.001) {
          double ang = std::atan2(py, px);
          pool.push_back({{contacts[0], contacts[1], contacts[2]}, cert, center, delta, u_ex, u_vec, ang});
        }
      }
    }
  }

  std::cout << "Collected " << pool.size() << " transverse candidates.\n";

  // Sort pool by transverse angle theta:
  std::sort(pool.begin(), pool.end(), [](const AxisCand& a, const AxisCand& b) {
    return a.theta < b.theta;
  });

  // Test pairs in the full pool:
  std::cout << "Testing all pairs in pool of size " << pool.size() << "...\n";
  double best_min_w = -1e9;
  size_t best_i = 0, best_j = 0;

  for (size_t i = 0; i < pool.size(); i++) {
    for (size_t j = i + 1; j < pool.size(); j++) {
      double w[4];
      if (SolveTetraOriginDouble(u0, u1, pool[i].u, pool[j].u, w)) {
        double min_w = std::min({w[0], w[1], w[2], w[3]});
        if (min_w > best_min_w) {
          best_min_w = min_w;
          best_i = i; best_j = j;
          std::cout << "New best min_w: " << best_min_w
                    << " (w0=" << w[0] << ", w1=" << w[1]
                    << ", w2=" << w[2] << ", w3=" << w[3] << ")\n";
          if (min_w > 0.0) {
            std::cout << "\n============================================\n";
            std::cout << "SUCCESS! ALL 4 WEIGHTS STRICTLY POSITIVE!\n";
            std::cout << "============================================\n";
            BigRat exact_w[4];
            SolveTetraOrigin(u0_exact, u1_exact, pool[i].u_exact, pool[j].u_exact, exact_w);
            std::cout << "  w0 = " << exact_w[0].ToString() << "\n";
            std::cout << "  w1 = " << exact_w[1].ToString() << "\n";
            std::cout << "  w2 = " << exact_w[2].ToString() << "\n";
            std::cout << "  w3 = " << exact_w[3].ToString() << "\n";
            std::cout << "Axis 2 contacts:\n";
            for (int m = 0; m < 3; m++) {
              auto c = pool[i].c[m];
              std::cout << "  {" << c.edge_start << ", " << c.edge_finish << ", "
                        << c.edge_start2 << ", " << c.edge_finish2 << ", "
                        << c.mix << ", " << c.vertex << "}\n";
            }
            std::cout << "Axis 3 contacts:\n";
            for (int m = 0; m < 3; m++) {
              auto c = pool[j].c[m];
              std::cout << "  {" << c.edge_start << ", " << c.edge_finish << ", "
                        << c.edge_start2 << ", " << c.edge_finish2 << ", "
                        << c.mix << ", " << c.vertex << "}\n";
            }
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Done testing pairs. Best min_w = " << best_min_w << "\n";
  std::cout << "Axis 2 contacts:\n";
  for (int m = 0; m < 3; m++) {
    auto c = pool[best_i].c[m];
    std::cout << "  {" << c.edge_start << ", " << c.edge_finish << ", "
              << c.edge_start2 << ", " << c.edge_finish2 << ", "
              << c.mix << ", " << c.vertex << "}\n";
  }
  std::cout << "Axis 3 contacts:\n";
  for (int m = 0; m < 3; m++) {
    auto c = pool[best_j].c[m];
    std::cout << "  {" << c.edge_start << ", " << c.edge_finish << ", "
              << c.edge_start2 << ", " << c.edge_finish2 << ", "
              << c.mix << ", " << c.vertex << "}\n";
  }
  return 0;
}
