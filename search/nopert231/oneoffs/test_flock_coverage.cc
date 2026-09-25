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

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  auto cap_pts = GenerateCapPoints(u0, alpha, 10000);

  std::vector<int> flock = {3063, 389, 3449, 213, 25};
  std::vector<vec3> flock_v;
  for (int idx : flock) {
    vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
    flock_v.push_back(v);
  }

  double min_dot = 1e9;
  for (const auto &p : cap_pts) {
    double m = -1e9;
    for (const auto &v : flock_v) {
      m = std::max(m, yocto::dot(p, v));
    }
    min_dot = std::min(min_dot, m);
  }

  std::cout << "Minimum flock dot over 10,000 points at c_cone = 0.025: " << min_dot << "\n";
  return 0;
}
