#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

using vec2 = yocto::vec<double, 2>;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

struct AxisInfo {
  ContactInfo contacts[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 dir;
};

static double Cross2D(const vec2 &a, const vec2 &b) {
  return a.x * b.y - a.y * b.x;
}

static bool TriangleContainsOrigin(const vec2 &a, const vec2 &b, const vec2 &c) {
  double c1 = Cross2D(a, b);
  double c2 = Cross2D(b, c);
  double c3 = Cross2D(c, a);
  return (c1 > 1e-4 && c2 > 1e-4 && c3 > 1e-4) ||
         (c1 < -1e-4 && c2 < -1e-4 && c3 < -1e-4);
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  std::cout << "Harvesting all zero-defect candidates...\n";
  std::vector<AxisInfo> pool;
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
        AxisInfo info;
        info.contacts[0] = contacts[0];
        info.contacts[1] = contacts[1];
        info.contacts[2] = contacts[2];
        info.cert = cert;
        info.center = center;
        info.delta = delta;
        info.dir = u_vec;
        pool.push_back(info);
      }
    }
  }

  std::cout << "Pool size: " << pool.size() << "\n";

  // Test Axis 4757 as Axis 0:
  int ax0_idx = 4757;
  const auto &ax0 = pool[ax0_idx];
  vec3 target_ray = -ax0.dir;

  vec3 temp = std::abs(target_ray.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(target_ray, temp));
  vec3 ey = yocto::cross(target_ray, ex);

  struct ProjPoint {
    int pool_idx;
    vec2 q;
    double dist;
  };

  std::vector<ProjPoint> proj;
  for (size_t i = 0; i < pool.size(); i++) {
    if ((int)i == ax0_idx) continue;
    double dot_t = yocto::dot(pool[i].dir, target_ray);
    if (dot_t > 0.05) {
      double qx = yocto::dot(pool[i].dir, ex) / dot_t;
      double qy = yocto::dot(pool[i].dir, ey) / dot_t;
      proj.push_back({(int)i, vec2{qx, qy}, std::hypot(qx, qy)});
    }
  }

  // Sort all projected points by angle in [0, 2pi)
  struct AngPoint {
    int pool_idx;
    vec2 q;
    double ang;
  };

  std::vector<AngPoint> pts;
  for (const auto &p : proj) {
    double ang = std::atan2(p.q.y, p.q.x);
    if (ang < 0) ang += 2 * M_PI;
    pts.push_back({p.pool_idx, p.q, ang});
  }

  std::sort(pts.begin(), pts.end(), [](const AngPoint &a, const AngPoint &b) {
    return a.ang < b.ang;
  });

  std::cout << "Sorted " << pts.size() << " points by angle.\n";
  std::cout << "\nSupport function in 36 directions:\n";
  int num_angles = 36;
  double min_supp = 1e9;
  for (int a = 0; a < num_angles; a++) {
    double theta = a * 2.0 * M_PI / num_angles;
    double dx = std::cos(theta);
    double dy = std::sin(theta);
    double max_p = -1e9;
    int best_p_idx = -1;
    for (size_t j = 0; j < pts.size(); j++) {
      double p = dx * pts[j].q.x + dy * pts[j].q.y;
      if (p > max_p) {
        max_p = p;
        best_p_idx = j;
      }
    }
    if (max_p < min_supp) min_supp = max_p;
    std::cout << "  theta = " << std::setw(5) << (theta * 180.0 / M_PI)
              << " deg: max_p = " << std::setw(10) << max_p
              << " (point " << best_p_idx << ", ang="
              << (pts[best_p_idx].ang * 180.0 / M_PI)
              << ", q=(" << pts[best_p_idx].q.x << "," << pts[best_p_idx].q.y << "))\n";
  }
  std::cout << "Overall min_supp = " << min_supp << "\n";
  int found = 0;
  return 0;
  for (size_t i = 0; i < pts.size(); i += 10) {
    for (size_t j = i + 1; j < pts.size(); j += 10) {
      double gap1 = pts[j].ang - pts[i].ang;
      if (gap1 >= M_PI) break; // j is too far ahead

      for (size_t k = j + 1; k < pts.size(); k += 10) {
        double gap2 = pts[k].ang - pts[j].ang;
        if (gap2 >= M_PI) break; // k is too far ahead

        double gap3 = (pts[i].ang + 2 * M_PI) - pts[k].ang;
        if (gap3 >= M_PI) continue; // gap3 too large

        // All 3 gaps < pi! Origin is strictly inside!
        found++;
        const auto &ax1 = pool[pts[i].pool_idx];
        const auto &ax2 = pool[pts[j].pool_idx];
        const auto &ax3 = pool[pts[k].pool_idx];

          BigRat box_c(1, 1000);
          BigRat box_delta(234013, 1000000000);
          BigRat c_cone(80, 1000); // 0.080

          BigVecQ3 u0 = ax0.center / ax0.cert.B;
          BigVecQ3 u1 = ax1.center / ax1.cert.B;
          BigVecQ3 u2 = ax2.center / ax2.cert.B;
          BigVecQ3 u3 = ax3.center / ax3.cert.B;

          BigRat scale0 = (box_c + box_delta) / c_cone;
          BigVecQ3 p0 = {scale0 * u0.x, scale0 * u0.y, scale0 * u0.z};
          BigVecQ3 p1 = u1;
          BigVecQ3 p2 = u2;
          BigVecQ3 p3 = u3;

          BigRat R = (BigRat(7, 4)) * (box_c + box_delta);
          std::vector<BigVecQ3> oct = {
            BigVecQ3{R, BigRat(0), BigRat(0)}, BigVecQ3{-R, BigRat(0), BigRat(0)},
            BigVecQ3{BigRat(0), R, BigRat(0)}, BigVecQ3{BigRat(0), -R, BigRat(0)},
            BigVecQ3{BigRat(0), BigRat(0), R}, BigVecQ3{BigRat(0), BigRat(0), -R}
          };

          bool oct_ok = true;
          for (int v = 0; v < 6; v++) {
            BigVecQ3 d1 = {p1.x - p0.x, p1.y - p0.y, p1.z - p0.z};
            BigVecQ3 d2 = {p2.x - p0.x, p2.y - p0.y, p2.z - p0.z};
            BigVecQ3 d3 = {p3.x - p0.x, p3.y - p0.y, p3.z - p0.z};

            BigVecQ3 c12 = {d1.y * d2.z - d1.z * d2.y, d1.z * d2.x - d1.x * d2.z, d1.x * d2.y - d1.y * d2.x};
            BigRat det = c12.x * d3.x + c12.y * d3.y + c12.z * d3.z;

            BigVecQ3 c23 = {d2.y * d3.z - d2.z * d3.y, d2.z * d3.x - d2.x * d3.z, d2.x * d3.y - d2.y * d3.x};
            BigVecQ3 c31 = {d3.y * d1.z - d3.z * d1.y, d3.z * d1.x - d3.x * d1.z, d3.x * d1.y - d3.y * d1.x};

            BigVecQ3 dp = {oct[v].x - p0.x, oct[v].y - p0.y, oct[v].z - p0.z};
            BigRat w1 = (dp.x * c23.x + dp.y * c23.y + dp.z * c23.z) / det;
            BigRat w2 = (dp.x * c31.x + dp.y * c31.y + dp.z * c31.z) / det;
            BigRat w3 = (dp.x * c12.x + dp.y * c12.y + dp.z * c12.z) / det;
            BigRat w0 = BigRat(1) - w1 - w2 - w3;

            if (w0 < 0 || w1 < 0 || w2 < 0 || w3 < 0) {
              oct_ok = false;
              break;
            }
          }

          if (oct_ok) {
            std::cout << "\n=======================================================\n";
            std::cout << "*** VICTORY! ALL 6 OCTAHEDRON VERTICES ARE POSITIVE! ***\n";
            std::cout << "Quad pool indices: {" << ax0_idx << ", "
                      << pts[i].pool_idx << ", " << pts[j].pool_idx << ", "
                      << pts[k].pool_idx << "}\n";
            std::cout << "=======================================================\n";
            return 0;
          }
      }
    }
  }

  std::cout << "Total enclosing triangles checked: " << found << "\n";
  return 0;
}
