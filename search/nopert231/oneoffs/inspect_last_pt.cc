#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

std::vector<vec3> GenerateCapPoints(const vec3 &u0, double alpha_rad, int num_points) {
  std::vector<vec3> pts;
  vec3 z = u0;
  vec3 x = yocto::normalize(yocto::cross(z, std::abs(z.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 y = yocto::cross(z, x);

  double cos_max = std::cos(alpha_rad);
  for (int i = 0; i < num_points; i++) {
    double t = (double)i / (double)(num_points - 1);
    double cos_theta = 1.0 - t * (1.0 - cos_max);
    double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
    double phi = i * 2.399963229728653;
    vec3 p = (std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z;
    pts.push_back(yocto::normalize(p));
  }
  return pts;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  auto cap_pts = GenerateCapPoints(u0, alpha, 4000);

  // 4 axes from flock:
  std::vector<int> flock_indices = {3054, 22, 3066, 3063};
  std::vector<vec3> flock_v;
  for (int idx : flock_indices) {
    vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
    flock_v.push_back(v);
  }

  double min_flock_dot = 1e9;
  int worst_pt = -1;
  for (size_t p = 0; p < cap_pts.size(); p++) {
    double max_dot = -1e9;
    for (const auto &v : flock_v) {
      max_dot = std::max(max_dot, yocto::dot(cap_pts[p], v));
    }
    if (max_dot < min_flock_dot) {
      min_flock_dot = max_dot;
      worst_pt = p;
    }
  }

  std::cout << "Minimum max_dot over 4000 points with 4 axes: " << min_flock_dot << " at point " << worst_pt << "\n";

  // Let's see if any other axis in all 5000 axes has higher dot product on worst_pt:
  double best_other_dot = -1e9;
  int best_other_axis = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(cap_pts[worst_pt], v);
    if (d > best_other_dot) {
      best_other_dot = d;
      best_other_axis = i;
    }
  }
  std::cout << "Best other axis on worst_pt: axis " << best_other_axis << " has dot " << best_other_dot << "\n";
  return 0;
}
