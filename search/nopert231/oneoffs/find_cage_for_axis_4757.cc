#include <iostream>
#include <iomanip>
#include <cmath>
#include <vector>
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

struct AxisInfo {
  ContactInfo contacts[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 dir;
};

using vec2 = yocto::vec<double, 2>;

// 2D cross product
static double Cross2D(const vec2 &a, const vec2 &b) {
  return a.x * b.y - a.y * b.x;
}

// Distance from (0,0) to edge a->b, positive if origin is to the left of directed edge
static double EdgeDist(const vec2 &a, const vec2 &b) {
  vec2 d = b - a;
  double len = std::hypot(d.x, d.y);
  if (len < 1e-12) return -1e9;
  return Cross2D(a, b) / len;
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
  std::cout << "Target ray (-ax0.dir): (" << target_ray.x << ", "
            << target_ray.y << ", " << target_ray.z << ")\n";

  vec3 temp = std::abs(target_ray.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(target_ray, temp));
  vec3 ey = yocto::cross(target_ray, ex);

  struct ProjPoint {
    int pool_idx;
    vec2 q;
    double angle;
  };

  std::vector<ProjPoint> proj;
  for (size_t i = 0; i < pool.size(); i++) {
    if ((int)i == ax0_idx) continue;
    double dot_t = yocto::dot(pool[i].dir, target_ray);
    if (dot_t > 0.1) {
      double qx = yocto::dot(pool[i].dir, ex) / dot_t;
      double qy = yocto::dot(pool[i].dir, ey) / dot_t;
      proj.push_back({(int)i, vec2{qx, qy}, std::atan2(qy, qx)});
    }
  }

  std::cout << "Points in forward hemisphere: " << proj.size() << "\n";

  // Bin into 36 angular bins, keeping the closest point to origin in each bin
  const int NUM_BINS = 36;
  std::vector<ProjPoint> binned(NUM_BINS);
  std::vector<bool> has_bin(NUM_BINS, false);

  for (const auto &p : proj) {
    double ang = p.angle;
    if (ang < 0) ang += 2 * M_PI;
    int b = (int)(ang / (2 * M_PI) * NUM_BINS) % NUM_BINS;
    double dist = std::hypot(p.q.x, p.q.y);
    if (!has_bin[b] || dist < std::hypot(binned[b].q.x, binned[b].q.y)) {
      binned[b] = p;
      has_bin[b] = true;
    }
  }

  std::vector<ProjPoint> filtered;
  for (int b = 0; b < NUM_BINS; b++) {
    if (has_bin[b]) filtered.push_back(binned[b]);
  }
  std::cout << "Filtered to " << filtered.size() << " representative points.\n";

  // Search for the triple that encloses (0,0) with maximum 2D inradius:
  double best_inradius = -1e9;
  int best_i = -1, best_j = -1, best_k = -1;

  for (size_t i = 0; i < filtered.size(); i++) {
    for (size_t j = i + 1; j < filtered.size(); j++) {
      for (size_t k = j + 1; k < filtered.size(); k++) {
        double d1 = EdgeDist(filtered[i].q, filtered[j].q);
        double d2 = EdgeDist(filtered[j].q, filtered[k].q);
        double d3 = EdgeDist(filtered[k].q, filtered[i].q);

        // All 3 edges must have origin on the same side:
        double inrad = std::min({d1, d2, d3});
        if (inrad <= 0) {
          // Check if reverse orientation:
          double inrad_rev = std::min({-d1, -d2, -d3});
          if (inrad_rev > inrad) inrad = inrad_rev;
        }

        if (inrad > best_inradius) {
          best_inradius = inrad;
          best_i = i;
          best_j = j;
          best_k = k;
        }
      }
    }
  }

  std::cout << "Best 2D inradius: " << best_inradius << "\n";
  std::cout << "Triangles indices: " << filtered[best_i].pool_idx << ", "
            << filtered[best_j].pool_idx << ", " << filtered[best_k].pool_idx << "\n";

  // Now verify exact barycentric coordinates of 6 octahedron vertices!
  const auto &ax1 = pool[filtered[best_i].pool_idx];
  const auto &ax2 = pool[filtered[best_j].pool_idx];
  const auto &ax3 = pool[filtered[best_k].pool_idx];

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

  std::cout << "\nExact Octahedron Barycentric Checks:\n";
  bool all_oct_ok = true;
  for (int v = 0; v < 6; v++) {
    BigRat w[4];
    // Solve sum w_j p_j = oct[v], sum w_j = 1
    // Using SolveTetraExact:
    BigVecQ3 d1 = {p1.x - p0.x, p1.y - p0.y, p1.z - p0.z};
    BigVecQ3 d2 = {p2.x - p0.x, p2.y - p0.y, p2.z - p0.z};
    BigVecQ3 d3 = {p3.x - p0.x, p3.y - p0.y, p3.z - p0.z};

    BigVecQ3 c12 = {d1.y * d2.z - d1.z * d2.y, d1.z * d2.x - d1.x * d2.z, d1.x * d2.y - d1.y * d2.x};
    BigRat det = c12.x * d3.x + c12.y * d3.y + c12.z * d3.z;

    BigVecQ3 c23 = {d2.y * d3.z - d2.z * d3.y, d2.z * d3.x - d2.x * d3.z, d2.x * d3.y - d2.y * d3.x};
    BigVecQ3 c31 = {d3.y * d1.z - d3.z * d1.y, d3.z * d1.x - d3.x * d1.z, d3.x * d1.y - d3.y * d1.x};

    BigVecQ3 dp = {oct[v].x - p0.x, oct[v].y - p0.y, oct[v].z - p0.z};
    w[1] = (dp.x * c23.x + dp.y * c23.y + dp.z * c23.z) / det;
    w[2] = (dp.x * c31.x + dp.y * c31.y + dp.z * c31.z) / det;
    w[3] = (dp.x * c12.x + dp.y * c12.y + dp.z * c12.z) / det;
    w[0] = BigRat(1) - w[1] - w[2] - w[3];

    std::cout << "Oct vertex " << v << ": w = ["
              << w[0].ToDouble() << ", " << w[1].ToDouble() << ", "
              << w[2].ToDouble() << ", " << w[3].ToDouble() << "]\n";
    for (int j = 0; j < 4; j++) {
      if (w[j] < 0) all_oct_ok = false;
    }
  }

  if (all_oct_ok) {
    std::cout << "\n========================================\n";
    std::cout << "VICTORY! ALL 6 OCTAHEDRON VERTICES ARE POSITIVE!\n";
    std::cout << "Quad: {" << ax0_idx << ", " << proj[best_i].pool_idx
              << ", " << proj[best_j].pool_idx << ", " << proj[best_k].pool_idx << "}\n";
    std::cout << "========================================\n";
  } else {
    std::cout << "\nSome vertices were negative.\n";
  }

  return 0;
}
