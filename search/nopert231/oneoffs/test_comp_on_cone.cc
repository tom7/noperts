#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Complement axes from tree_0:
  // Cert 1: {15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}
  ContactInfo c1[3] = {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}};
  // Cert 2: {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}
  ContactInfo c2[3] = {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}};
  // Cert 3: {3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}
  ContactInfo c3[3] = {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}};

  ContactInfo c_ann[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};

  AxisCertificate certs[4];
  BigVecQ3 centers[4];
  BigRat deltas[4];
  Tube229::AuditAxis(tri, c_ann, &certs[0], &centers[0], &deltas[0], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &certs[1], &centers[1], &deltas[1], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &certs[2], &centers[2], &deltas[2], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &certs[3], &centers[3], &deltas[3], &err, BigRat(5, 1000));

  vec3 u[4];
  for (int m = 0; m < 4; m++) {
    u[m] = yocto::normalize(vec3{centers[m].x.ToDouble(), centers[m].y.ToDouble(), centers[m].z.ToDouble()});
    std::cout << "u[" << m << "] = (" << u[m].x << ", " << u[m].y << ", " << u[m].z << ")\n";
  }

  vec3 u0 = u[0];
  vec3 e1 = yocto::normalize(yocto::cross(u0, vec3{0, 1, 0}));
  vec3 e2 = yocto::normalize(yocto::cross(u0, e1));
  double c_cone = 0.2;
  double R_disk = std::sqrt(1.0 - c_cone * c_cone);
  int N = 12;
  double R_poly = R_disk / std::cos(M_PI / N);
  vec3 center_pt = c_cone * u0;

  for (int k = 0; k < N; k++) {
    double angle = 2.0 * M_PI * k / N;
    vec3 v = center_pt + R_poly * (std::cos(angle) * e1 + std::sin(angle) * e2);
    vec3 v_hat = yocto::normalize(v);
    std::cout << "Ray " << k << " (angle " << (angle * 180 / M_PI) << " deg): ";
    std::cout << "dots with u1, u2, u3: "
              << yocto::dot(v_hat, u[1]) << ", "
              << yocto::dot(v_hat, u[2]) << ", "
              << yocto::dot(v_hat, u[3]) << "\n";
  }

  return 0;
}
