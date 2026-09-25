#include <iostream>
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

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Axis 0 from test_full_box_03121303200.lean:
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

  std::cout << "Harvesting all zero-defect candidates...\n";
  std::vector<vec3> pool;
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
        pool.push_back(u_vec);
      }
    }
  }

  std::cout << "Total zero-defect axes: " << pool.size() << "\n";

  // Check if target_ray = -u0 is in the positive cone of pool:
  // Using Frank-Wolfe / Gilbert's algorithm to find closest point in cone(pool) to target_ray:
  // We want to minimize || sum lambda_i v_i - target_ray ||^2 with lambda_i >= 0.
  // Start with best single vector:
  int best_init = 0;
  double best_dot = -1.0;
  for (size_t i = 0; i < pool.size(); i++) {
    double d = yocto::dot(pool[i], target_ray);
    if (d > best_dot) {
      best_dot = d;
      best_init = i;
    }
  }

  std::cout << "Max dot product with -u0: " << best_dot
            << " (angle = " << (std::acos(std::min(1.0, best_dot)) * 180.0 / M_PI) << " deg)\n";

  // Let's run a projection test onto tangent plane of -u0:
  vec3 temp = std::abs(target_ray.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(target_ray, temp));
  vec3 ey = yocto::cross(target_ray, ex);

  // Check 2D convex hull of projected points:
  // For any 2D angle theta in [0, 2pi), what is max (cos(theta)*x + sin(theta)*y)?
  // If max > 0 for all theta, then (0,0) is in interior of 2D convex hull!
  int num_angles = 360;
  double min_support = 1e9;
  double worst_angle = 0;

  for (int a = 0; a < num_angles; a++) {
    double theta = a * 2.0 * M_PI / num_angles;
    double dir_x = std::cos(theta);
    double dir_y = std::sin(theta);

    double max_proj = -1e9;
    for (const auto& v : pool) {
      double dot_t = yocto::dot(v, target_ray);
      if (dot_t > 0.01) { // in hemisphere
        double qx = yocto::dot(v, ex) / dot_t;
        double qy = yocto::dot(v, ey) / dot_t;
        double proj = dir_x * qx + dir_y * qy;
        if (proj > max_proj) max_proj = proj;
      }
    }

    if (max_proj < min_support) {
      min_support = max_proj;
      worst_angle = theta;
    }
  }

  std::cout << "Support function minimum over all directions: " << min_support << "\n";
  if (min_support > 0) {
    std::cout << "CONFIRMED: -u0 is in the STRICT INTERIOR of cone(pool)! Margin = "
              << min_support << "\n";
  } else {
    std::cout << "Separating direction found at angle " << (worst_angle * 180.0 / M_PI)
              << " deg! Support = " << min_support << "\n";
  }

  return 0;
}
