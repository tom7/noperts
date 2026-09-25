#include <iostream>
#include <iomanip>
#include <vector>
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

static inline bool SolveTetraOriginDouble(const vec3& p0, const vec3& p1,
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

  double inv_det = 1.0 / det;
  double d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  double d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  double d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 * inv_det;
  w[1] = d1 * inv_det;
  w[2] = d2 * inv_det;
  w[3] = 1.0 - w[0] - w[1] - w[2];
  return true;
}

static bool SolveTetraTarget(const BigVecQ3& p0, const BigVecQ3& p1,
                             const BigVecQ3& p2, const BigVecQ3& p3,
                             const BigVecQ3& target,
                             BigRat b[4]) {
  BigRat M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  BigRat rhs[3] = {target.x - p3.x, target.y - p3.y, target.z - p3.z};

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

  b[0] = d0 / det;
  b[1] = d1 / det;
  b[2] = d2 / det;
  b[3] = BigRat(1) - b[0] - b[1] - b[2];
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Box parameters for Lean:
  BigRat box_c = BigRat(1, 1000);
  BigRat box_delta = BigRat(234013, 1000000000);
  BigRat c_cone = BigRat(15, 1000);
  BigRat R = BigRat(7, 4) * (box_c + box_delta);
  BigVecQ3 oct[6] = {
    {R, BigRat(0), BigRat(0)},
    {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)},
    {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R},
    {BigRat(0), BigRat(0), -R}
  };

  // Base u0, u1:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 420, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 425, 15)
  };
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 600, 15),
    MakeContact(19, 3, 3, 2, 740, 3)
  };

  AxisCertificate ax0, ax1;
  BigVecQ3 cnt0, cnt1;
  BigRat del0, del1;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0));
  Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &del1, &err, BigRat(0));

  BigVecQ3 u0_ex = cnt0 / ax0.B;
  BigVecQ3 p0_ex = u0_ex * ((box_c + box_delta) / c_cone);
  BigVecQ3 u1_ex = cnt1 / ax1.B;

  vec3 p0 = {p0_ex.x.ToDouble(), p0_ex.y.ToDouble(), p0_ex.z.ToDouble()};
  vec3 p1 = {u1_ex.x.ToDouble(), u1_ex.y.ToDouble(), u1_ex.z.ToDouble()};

  std::cout << "Harvesting all zero-defect candidates...\n";
  struct Cand {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigVecQ3 u_ex;
    vec3 u_vec;
  };
  std::vector<Cand> pool;

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
        pool.push_back({ {contacts[0], contacts[1], contacts[2]}, cert, center, u_ex, u_vec });
      }
    }
  }

  std::cout << "Pool size: " << pool.size() << "\n";
  std::cout << "Testing all pairs (u2, u3)...\n";

  double best_min_w = -1e9;

  for (size_t i = 0; i < pool.size(); i++) {
    const vec3& p2 = pool[i].u_vec;
    for (size_t j = i + 1; j < pool.size(); j++) {
      const vec3& p3 = pool[j].u_vec;

      double w[4];
      if (!SolveTetraOriginDouble(p0, p1, p2, p3, w)) continue;

      double min_w = std::min({w[0], w[1], w[2], w[3]});
      if (min_w > best_min_w) {
        best_min_w = min_w;
        std::cout << "New best (" << i << ", " << j << "): min_w = " << min_w
                  << " (w0=" << w[0] << ", w1=" << w[1]
                  << ", w2=" << w[2] << ", w3=" << w[3] << ")\n";

        if (min_w > 0.0) {
          std::cout << "\nFOUND STRICTLY POSITIVE CAGE! Verifying octahedron targets...\n";
          bool oct_ok = true;
          for (int t = 0; t < 6; t++) {
            BigRat b[4];
            if (!SolveTetraTarget(p0_ex, u1_ex, pool[i].u_ex, pool[j].u_ex, oct[t], b)) {
              oct_ok = false; break;
            }
            for (int c = 0; c < 4; c++) {
              if (b[c] <= BigRat(0)) { oct_ok = false; break; }
            }
            if (!oct_ok) break;
          }
          if (oct_ok) {
            std::cout << "========================================================\n";
            std::cout << "SUCCESS! COMPLETE DECOMPOSED CERTIFICATE VERIFIED!\n";
            std::cout << "Axis 2 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  {" << pool[i].contacts[c].edge_start << ", "
                        << pool[i].contacts[c].edge_finish << ", "
                        << pool[i].contacts[c].edge_start2 << ", "
                        << pool[i].contacts[c].edge_finish2 << ", "
                        << pool[i].contacts[c].mix << ", "
                        << pool[i].contacts[c].vertex << "}\n";
            }
            std::cout << "Axis 3 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  {" << pool[j].contacts[c].edge_start << ", "
                        << pool[j].contacts[c].edge_finish << ", "
                        << pool[j].contacts[c].edge_start2 << ", "
                        << pool[j].contacts[c].edge_finish2 << ", "
                        << pool[j].contacts[c].mix << ", "
                        << pool[j].contacts[c].vertex << "}\n";
            }
            std::cout << "========================================================\n";
            return 0;
          } else {
            std::cout << "Octahedron targets failed.\n";
          }
        }
      }
    }
  }

  std::cout << "Finished testing all pairs. Best min_w = " << best_min_w << "\n";
  return 0;
}
