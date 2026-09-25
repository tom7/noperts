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

  // k1, k2 orthonormal to u0
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::normalize(yocto::cross(u0, k1));

  double c_cone = 0.025;
  double c_core = 0.0001;

  std::vector<int> flock = {3063, 389, 3449, 213, 25};
  std::vector<vec3> flock_v;
  for (int idx : flock) {
    vec3 v = vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                  axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()};
    flock_v.push_back(v);
  }

  // Decompose each v in (k1, k2, u0):
  // Since k1, k2 are unit and perp to u0:
  // v = c1 k1 + c2 k2 + c0 u0
  // v . k1 = c1
  // v . k2 = c2
  // v . u0 = c0 * ||u0||^2  => c0 = (v . u0) / ||u0||^2
  std::vector<double> c1(flock.size()), c2(flock.size()), coeff0(flock.size());
  double u0_sq = yocto::length_squared(u0);
  for (size_t m = 0; m < flock.size(); m++) {
    c1[m] = yocto::dot(flock_v[m], k1);
    c2[m] = yocto::dot(flock_v[m], k2);
    coeff0[m] = yocto::dot(flock_v[m], u0) / u0_sq;
    std::cout << "Axis " << m << ": c1=" << c1[m] << ", c2=" << c2[m] << ", c0=" << coeff0[m] << "\n";
  }

  // Test grid of boxes on [-1, 1]^2
  for (int G : {2, 3, 4, 5, 6, 8, 10, 12, 16}) {
    double step = 2.0 / G;
    bool all_covered = true;
    int covered_boxes = 0;

    for (int ix = 0; ix < G; ix++) {
      double x_min = -1.0 + ix * step;
      double x_max = x_min + step;
      for (int iy = 0; iy < G; iy++) {
        double y_min = -1.0 + iy * step;
        double y_max = y_min + step;

        // Check if box intersects the disk x^2 + y^2 <= 1:
        // Distance from origin to box:
        double dx = (x_min > 0) ? x_min : (x_max < 0 ? -x_max : 0.0);
        double dy = (y_min > 0) ? y_min : (y_max < 0 ? -y_max : 0.0);
        if (dx * dx + dy * dy > 1.0) continue; // Outside unit disk

        // Check if any axis covers this box:
        bool box_ok = false;
        for (size_t m = 0; m < flock.size(); m++) {
          if (coeff0[m] < 0) continue;
          double corner = (c1[m] >= 0 ? c1[m] * x_min : c1[m] * x_max) +
                          (c2[m] >= 0 ? c2[m] * y_min : c2[m] * y_max) +
                          coeff0[m] * c_cone;
          if (corner >= c_core) {
            box_ok = true;
            break;
          }
        }
        if (!box_ok) {
          all_covered = false;
        } else {
          covered_boxes++;
        }
      }
    }
    std::cout << "Grid " << G << "x" << G << ": all_covered=" << (all_covered ? "YES" : "no")
              << " (" << covered_boxes << " boxes valid)\n";
    if (all_covered) break;
  }

  return 0;
}
