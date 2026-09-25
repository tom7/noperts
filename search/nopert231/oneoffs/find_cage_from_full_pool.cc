#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

struct AxisInfo {
  ContactInfo contacts[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 dir; // normalized center
};

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

  std::cout << "Total zero-defect axes in pool: " << pool.size() << "\n";
  vec3 mean_dir{0, 0, 0};
  for (const auto &p : pool) mean_dir += p.dir;
  mean_dir /= pool.size();
  std::cout << "Mean direction of pool: (" << mean_dir.x << ", " << mean_dir.y << ", " << mean_dir.z
            << "), length = " << yocto::length(mean_dir) << "\n";

  // For each axis in pool, test if -dir is in the strict interior of the cone of the pool
  // by checking the support function in 36 directions on the tangent plane.
  int enclosed_count = 0;
  double best_margin = -1e9;
  int best_idx = -1;

  for (size_t i = 0; i < pool.size(); i++) {
    vec3 target_ray = -pool[i].dir;
    vec3 temp = std::abs(target_ray.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
    vec3 ex = yocto::normalize(yocto::cross(target_ray, temp));
    vec3 ey = yocto::cross(target_ray, ex);

    std::vector<double> angles;
    for (size_t j = 0; j < pool.size(); j++) {
      if (i == j) continue;
      double dot_t = yocto::dot(pool[j].dir, target_ray);
      if (dot_t > 0.01) { // in forward hemisphere
        double qx = yocto::dot(pool[j].dir, ex);
        double qy = yocto::dot(pool[j].dir, ey);
        double ang = std::atan2(qy, qx);
        if (ang < 0) ang += 2 * M_PI;
        angles.push_back(ang);
      }
    }

    if (angles.size() < 3) continue;
    std::sort(angles.begin(), angles.end());

    double max_gap = (angles.front() + 2 * M_PI) - angles.back();
    for (size_t k = 0; k + 1 < angles.size(); k++) {
      double gap = angles[k + 1] - angles[k];
      if (gap > max_gap) max_gap = gap;
    }

    // Origin is strictly inside iff max_gap < M_PI!
    if (max_gap < M_PI) {
      enclosed_count++;
      double margin = (M_PI - max_gap) * 180.0 / M_PI;
      if (margin > best_margin) {
        best_margin = margin;
        best_idx = i;
      }
    }
  }

  std::cout << "Axes whose -dir is in STRICT INTERIOR of cone(pool): "
            << enclosed_count << " / " << pool.size() << "\n";
  std::cout << "Best margin = " << best_margin << " (at axis " << best_idx << ")\n";

  return 0;
}
