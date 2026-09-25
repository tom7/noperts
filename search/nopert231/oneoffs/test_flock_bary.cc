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
  vec3 u0 = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                 ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                 ann_center.z.ToDouble() / ann_cert.B.ToDouble()};

  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::normalize(yocto::cross(u0, k1));
  vec3 u0_hat = yocto::normalize(u0);

  double c_core = 0.0003;
  double scale = (7.0 / 4.0) * c_core;

  std::vector<vec3> test_pts = {
    scale * u0_hat,
    scale * k1,
    -scale * k1,
    scale * k2,
    -scale * k2
  };

  // Flock axes
  std::vector<int> flock = {3063, 389, 3449, 213, 25};
  std::vector<vec3> flock_v;
  for (int idx : flock) {
    vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
    flock_v.push_back(v);
  }

  std::cout << "Flock vectors:\n";
  for (size_t m = 0; m < flock_v.size(); m++) {
    std::cout << "v" << m << ": " << flock_v[m].x << ", " << flock_v[m].y << ", " << flock_v[m].z
              << " (norm=" << yocto::length(flock_v[m]) << ")\n";
  }

  std::cout << "\nTest points (scale=" << scale << "):\n";
  for (size_t k = 0; k < test_pts.size(); k++) {
    std::cout << "p" << k << ": " << test_pts[k].x << ", " << test_pts[k].y << ", " << test_pts[k].z << "\n";
  }

  return 0;
}
