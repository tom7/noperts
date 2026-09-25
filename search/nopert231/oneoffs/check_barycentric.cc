#include <iostream>
#include <iomanip>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct MyVec3 {
  double x, y, z;
  double dot(const MyVec3 &o) const { return x*o.x + y*o.y + z*o.z; }
  double norm_sq() const { return dot(*this); }
  static MyVec3 cross(const MyVec3 &a, const MyVec3 &b) {
    return {a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x};
  }
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo contacts[4][3] = {
    { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14} },
    { {2, 10, 10, 2, 0, 1}, {1, 15, 15, 1, 333, 15}, {4, 19, 19, 4, 333, 1} },
    { {2, 10, 10, 3, 0, 1}, {1, 15, 15, 2, 666, 15}, {4, 19, 19, 1, 0, 2} },
    { {2, 1, 1, 15, 0, 1}, {1, 4, 4, 19, 333, 4}, {4, 8, 8, 3, 1000, 19} }
  };

  MyVec3 u[4];
  for (int j = 0; j < 4; j++) {
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    Tube229::AuditAxis(tri, contacts[j], &ax, &ctr, &del, &err, BigRat(1, 1000));
    u[j] = {ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()};
    std::cout << "u[" << j << "]: (" << u[j].x << ", " << u[j].y << ", " << u[j].z << ")\n";
  }

  // Octahedron targets: 7/4 * (c + delta) * (±e_x, ±e_y, ±e_z)
  double c = 0.001;
  double delta = 0.000234013;
  double oct_radius = 1.75 * (c + delta);
  MyVec3 oct[6] = {
    {oct_radius, 0, 0}, {-oct_radius, 0, 0},
    {0, oct_radius, 0}, {0, -oct_radius, 0},
    {0, 0, oct_radius}, {0, 0, -oct_radius}
  };

  for (double c_cone : {0.005, 0.010, 0.015, 0.020, 0.025, 0.030, 0.035, 0.040, 0.045, 0.050, 0.055, 0.060, 0.065, 0.070}) {
    double scale0 = (c + delta) / c_cone;
    MyVec3 v0 = {scale0 * u[0].x, scale0 * u[0].y, scale0 * u[0].z};
    MyVec3 v1 = u[1];
    MyVec3 v2 = u[2];
    MyVec3 v3 = u[3];

    // Compute determinant of matrix [v0 1; v1 1; v2 1; v3 1]
    // Or solve for barycentric coordinates of each target
    // A * [b0; b1; b2; b3] = [target; 1]
    // where columns of A are [vi; 1]
    bool all_valid = true;
    for (int k = 0; k < 6; k++) {
      // 3x3 linear system for bi relative to v3:
      // (v0 - v3) b0 + (v1 - v3) b1 + (v2 - v3) b2 = target - v3
      MyVec3 d0 = {v0.x - v3.x, v0.y - v3.y, v0.z - v3.z};
      MyVec3 d1 = {v1.x - v3.x, v1.y - v3.y, v1.z - v3.z};
      MyVec3 d2 = {v2.x - v3.x, v2.y - v3.y, v2.z - v3.z};
      MyVec3 rhs = {oct[k].x - v3.x, oct[k].y - v3.y, oct[k].z - v3.z};

      double det = d0.dot(MyVec3::cross(d1, d2));
      double b0 = rhs.dot(MyVec3::cross(d1, d2)) / det;
      double b1 = d0.dot(MyVec3::cross(rhs, d2)) / det;
      double b2 = d0.dot(MyVec3::cross(d1, rhs)) / det;
      double b3 = 1.0 - b0 - b1 - b2;

      if (b0 < -1e-9 || b1 < -1e-9 || b2 < -1e-9 || b3 < -1e-9) {
        all_valid = false;
        break;
      }
    }
    std::cout << "c_cone=" << std::fixed << std::setprecision(3) << c_cone
              << ": barycentric valid = " << all_valid << "\n";
  }

  return 0;
}
