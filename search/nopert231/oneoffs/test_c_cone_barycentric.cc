#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_ann[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  ContactInfo c1[3] = {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}};
  ContactInfo c2[3] = {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}};
  ContactInfo c3[3] = {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}};

  AxisCertificate certs[4];
  BigVecQ3 centers[4];
  BigRat deltas[4];
  Tube229::AuditAxis(tri, c_ann, &certs[0], &centers[0], &deltas[0], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &certs[1], &centers[1], &deltas[1], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &certs[2], &centers[2], &deltas[2], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &certs[3], &centers[3], &deltas[3], &err, BigRat(5, 1000));

  vec3 u[4];
  for (int m = 0; m < 4; m++) {
    u[m] = {centers[m].x.ToDouble() / certs[m].B.ToDouble(),
            centers[m].y.ToDouble() / certs[m].B.ToDouble(),
            centers[m].z.ToDouble() / certs[m].B.ToDouble()};
  }

  double box_c = 0.001;
  double box_delta = 3.33e-7;

  // Check which c_cone has all barycentric coordinates >= 0 for the 6 octahedron vertices:
  vec3 oct[6] = {
    {box_c, 0, 0}, {-box_c, 0, 0},
    {0, box_c, 0}, {0, -box_c, 0},
    {0, 0, box_c}, {0, 0, -box_c}
  };

  for (double c_cone = 0.01; c_cone <= 0.95; c_cone += 0.02) {
    vec3 v[4];
    v[0] = ((box_c + box_delta) / c_cone) * u[0];
    v[1] = u[1];
    v[2] = u[2];
    v[3] = u[3];

    // Compute barycentric coords of oct[k] with respect to v[0], v[1], v[2], v[3]
    // A [b0, b1, b2, b3]^T = [p_x, p_y, p_z, 1]^T
    // where columns of A are [v_j; 1]
    bool valid = true;
    for (int k = 0; k < 6; k++) {
      // 4x4 matrix solve
      // Let's check determinant and min coordinate
      // Using standard Cramer's rule / linear algebra
      yocto::mat4f M = {
        { (float)v[0].x, (float)v[1].x, (float)v[2].x, (float)v[3].x },
        { (float)v[0].y, (float)v[1].y, (float)v[2].y, (float)v[3].y },
        { (float)v[0].z, (float)v[1].z, (float)v[2].z, (float)v[3].z },
        { 1.0f, 1.0f, 1.0f, 1.0f }
      };
      // invert M
      auto invM = yocto::inverse(M);
      yocto::vec4f pt = {(float)oct[k].x, (float)oct[k].y, (float)oct[k].z, 1.0f};
      yocto::vec4f bary = invM * pt;
      if (bary.x < -1e-6 || bary.y < -1e-6 || bary.z < -1e-6 || bary.w < -1e-6) {
        valid = false;
        break;
      }
    }
    if (valid) {
      std::cout << "c_cone = " << c_cone << " VALID for barycentric!\n";
    }
  }

  return 0;
}
