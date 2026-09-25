#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>
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
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * rhs[2]) +
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

struct Point2D {
  double x, y;
  int cand_idx;
};

// Check if (0,0) is in interior of triangle (p1, p2, p3):
static inline bool TriangleContainsOrigin(const Point2D& a, const Point2D& b, const Point2D& c, double min_cross = 1e-4) {
  double c1 = a.x * b.y - a.y * b.x;
  double c2 = b.x * c.y - b.y * c.x;
  double c3 = c.x * a.y - c.y * a.x;
  return (c1 > min_cross && c2 > min_cross && c3 > min_cross) ||
         (c1 < -min_cross && c2 < -min_cross && c3 < -min_cross);
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // u0 from test_full_box_03121303200.lean:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 280, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 395, 15)
  };
  AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0));
  BigVecQ3 u0_ex = cnt0 / ax0.B;
  vec3 u0 = yocto::normalize(vec3{u0_ex.x.ToDouble(), u0_ex.y.ToDouble(), u0_ex.z.ToDouble()});
  vec3 target_ray = -u0;

  // Build orthonormal basis (ex, ey, target_ray):
  vec3 temp = std::abs(target_ray.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(target_ray, temp));
  vec3 ey = yocto::cross(target_ray, ex);

  std::cout << "Harvesting zero-defect candidates...\n";
  struct Cand {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigVecQ3 u_ex;
    vec3 u_vec;
  };

  std::vector<Cand> pool;
  std::vector<Point2D> pts;

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
        vec3 u_vec = yocto::normalize(vec3{u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()});
        double dot_t = yocto::dot(u_vec, target_ray);
        if (dot_t > 0.05) { // In forward hemisphere
          double qx = yocto::dot(u_vec, ex) / dot_t;
          double qy = yocto::dot(u_vec, ey) / dot_t;
          int idx = (int)pool.size();
          pool.push_back({ {contacts[0], contacts[1], contacts[2]}, cert, center, u_ex, u_vec });
          pts.push_back({ qx, qy, idx });
        }
      }
    }
  }

  std::cout << "Points in gnomonic projection: " << pts.size() << "\n";
  int q1 = 0, q2 = 0, q3 = 0, q4 = 0;
  for (const auto& p : pts) {
    if (p.x >= 0 && p.y >= 0) q1++;
    else if (p.x < 0 && p.y >= 0) q2++;
    else if (p.x < 0 && p.y < 0) q3++;
    else q4++;
  }
  std::cout << "Quadrant counts: Q1(+,+)=" << q1 << " Q2(-,+)=" << q2
            << " Q3(-,-)=" << q3 << " Q4(+,-)=" << q4 << "\n";

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

  BigVecQ3 p0 = u0_ex * ((box_c + box_delta) / c_cone);

  // Search for triangles containing (0,0):
  // Sort points by distance from origin to prefer axes close to -u0:
  std::sort(pts.begin(), pts.end(), [](const Point2D& a, const Point2D& b) {
    return (a.x * a.x + a.y * a.y) < (b.x * b.x + b.y * b.y);
  });

  std::cout << "Searching for enclosing triples...\n";
  int M = std::min((int)pts.size(), 300);
  for (int i = 0; i < M; i++) {
    for (int j = i + 1; j < M; j++) {
      for (int k = j + 1; k < M; k++) {
        if (!TriangleContainsOrigin(pts[i], pts[j], pts[k], 0.001)) continue;

        // Origin is in triangle! Now verify in exact BigRat arithmetic:
        const auto& c1 = pool[pts[i].cand_idx];
        const auto& c2 = pool[pts[j].cand_idx];
        const auto& c3 = pool[pts[k].cand_idx];

        BigRat w[4];
        if (!SolveTetraOrigin(p0, c1.u_ex, c2.u_ex, c3.u_ex, w)) continue;

        if (w[0] > BigRat(0) && w[1] > BigRat(0) && w[2] > BigRat(0) && w[3] > BigRat(0)) {
          // Check all 6 octahedron targets!
          bool oct_ok = true;
          double min_oct_b = 1.0;
          for (int t = 0; t < 6; t++) {
            BigRat b[4];
            if (!SolveTetraTarget(p0, c1.u_ex, c2.u_ex, c3.u_ex, oct[t], b)) {
              oct_ok = false; break;
            }
            for (int coord = 0; coord < 4; coord++) {
              if (b[coord] <= BigRat(0)) {
                oct_ok = false; break;
              }
              min_oct_b = std::min(min_oct_b, b[coord].ToDouble());
            }
            if (!oct_ok) break;
          }

          if (oct_ok) {
            std::cout << "\n======================================================\n";
            std::cout << "SUCCESS! FOUND COMPLETE CAGE SATISFYING OCTAHEDRON TARGETS!\n";
            std::cout << "Origin barycentric weights:\n";
            std::cout << "  w0 = " << w[0].ToDouble() << "\n";
            std::cout << "  w1 = " << w[1].ToDouble() << "\n";
            std::cout << "  w2 = " << w[2].ToDouble() << "\n";
            std::cout << "  w3 = " << w[3].ToDouble() << "\n";
            std::cout << "Min octahedron barycentric coordinate: " << min_oct_b << "\n";

            std::cout << "\nAxis 1 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  {" << c1.contacts[c].edge_start << ", "
                        << c1.contacts[c].edge_finish << ", "
                        << c1.contacts[c].edge_start2 << ", "
                        << c1.contacts[c].edge_finish2 << ", "
                        << c1.contacts[c].mix << ", "
                        << c1.contacts[c].vertex << "}\n";
            }
            std::cout << "Axis 2 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  {" << c2.contacts[c].edge_start << ", "
                        << c2.contacts[c].edge_finish << ", "
                        << c2.contacts[c].edge_start2 << ", "
                        << c2.contacts[c].edge_finish2 << ", "
                        << c2.contacts[c].mix << ", "
                        << c2.contacts[c].vertex << "}\n";
            }
            std::cout << "Axis 3 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  {" << c3.contacts[c].edge_start << ", "
                        << c3.contacts[c].edge_finish << ", "
                        << c3.contacts[c].edge_start2 << ", "
                        << c3.contacts[c].edge_finish2 << ", "
                        << c3.contacts[c].mix << ", "
                        << c3.contacts[c].vertex << "}\n";
            }
            std::cout << "======================================================\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "No enclosure found in top " << M << " points.\n";
  return 0;
}
