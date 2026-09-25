#include <iostream>
#include <vector>
#include <cmath>
#include <array>
#include "tubetree229.h"
#include "yocto-math.h"
#include "nopert229.h"

using namespace tubetree229;
using vec3 = yocto::vec<double, 3>;
using vec2 = yocto::vec<double, 2>;

static inline vec3 FibSphere(int i, int n) {
  double phi = 2.0 * M_PI * i / 1.618033988749895;
  double z = 1.0 - (2.0 * i + 1.0) / n;
  double r = std::sqrt(std::max(0.0, 1.0 - z * z));
  return {r * std::cos(phi), r * std::sin(phi), z};
}

// Compute normalized variation vector for an axis certificate at view point v
static vec3 ComputeVariation(const TriangleQ &tri, const AxisCertificate &cert, const vec3 &view) {
  // Vertices of Nopert 229
  const auto &vertsQ = GetVerticesQ();
  std::vector<vec3> V(20);
  for (int i = 0; i < 20; i++) {
    V[i] = {vertsQ[i][0].ToDouble(), vertsQ[i][1].ToDouble(), vertsQ[i][2].ToDouble()};
  }

  // 2D projection frame for view vector
  vec3 z_cam = yocto::normalize(view);
  vec3 up = {0, 0, 1};
  if (std::abs(z_cam.z) > 0.99) up = {1, 0, 0};
  vec3 x_cam = yocto::normalize(yocto::cross(up, z_cam));
  vec3 y_cam = yocto::cross(z_cam, x_cam);

  auto proj2d = [&](const vec3 &p) -> vec2 {
    return {yocto::dot(p, x_cam), yocto::dot(p, y_cam)};
  };

  // Contacts
  vec3 total_var = {0, 0, 0};
  for (int m = 0; m < 3; m++) {
    const auto &c = cert.contacts[m];
    vec3 e1_s = V[c.edge_start];
    vec3 e1_f = V[c.edge_finish];
    vec3 e2_s = V[c.edge_start2];
    vec3 e2_f = V[c.edge_finish2];
    double mix = c.mix / 1000.0;

    vec2 d1 = proj2d(e1_f - e1_s);
    vec2 d2 = proj2d(e2_f - e2_s);
    // Outward normal to edge is (-d.y, d.x)
    vec2 n1 = {-d1.y, d1.x};
    vec2 n2 = {-d2.y, d2.x};
    if (yocto::length(n1) > 1e-9) n1 = yocto::normalize(n1);
    if (yocto::length(n2) > 1e-9) n2 = yocto::normalize(n2);
    vec2 normal2d = yocto::normalize(n1 * (1.0 - mix) + n2 * mix);

    // Normal in 3D: normal2d.x * x_cam + normal2d.y * y_cam
    vec3 normal3d = x_cam * normal2d.x + y_cam * normal2d.y;

    // Contact vertex
    vec3 v_cont = V[c.vertex];

    // Torque / variation = cross(v_cont, normal3d)
    vec3 torque = yocto::cross(v_cont, normal3d);
    total_var += torque; // approximate unweighted or weighted sum
  }

  double B = cert.B.ToDouble();
  if (B > 1e-9) {
    return total_var / B;
  }
  return total_var;
}

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 c0 = {tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()};
  vec3 c1 = {tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()};
  vec3 c2 = {tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()};
  vec3 center = yocto::normalize(c0 + c1 + c2);

  std::cout << "Triangle " << path << " center: " << center.x << ", " << center.y << ", " << center.z << "\n";

  // Define cert_hull
  AxisCertificate cert_hull;
  cert_hull.contacts[0] = {3, 2, 2, 1, 800, 2};
  cert_hull.contacts[1] = {1, 4, 4, 8, 800, 4};
  cert_hull.contacts[2] = {10, 15, 15, 19, 800, 15};
  cert_hull.nonzero_witness[0] = 9; cert_hull.nonzero_witness[1] = 15; cert_hull.nonzero_witness[2] = 1;
  cert_hull.B = BigRat(18061, 10000);

  // Define cert1, cert2, cert3
  AxisCertificate cert1, cert2, cert3;
  cert1.contacts[0] = {15, 19, 19, 3, 200, 19};
  cert1.contacts[1] = {2, 1, 1, 4, 200, 1};
  cert1.contacts[2] = {8, 9, 9, 10, 200, 9};
  cert1.nonzero_witness[0] = 8; cert1.nonzero_witness[1] = 15; cert1.nonzero_witness[2] = 2;
  cert1.B = BigRat(898481993, 1000000000);

  cert2.contacts[0] = {2, 1, 1, 4, 0, 1};
  cert2.contacts[1] = {10, 15, 15, 19, 333, 15};
  cert2.contacts[2] = {10, 15, 15, 19, 0, 15};
  cert2.nonzero_witness[0] = 15; cert2.nonzero_witness[1] = 1; cert2.nonzero_witness[2] = 4;
  cert2.B = BigRat(254450361, 500000000);

  cert3.contacts[0] = {3, 2, 2, 1, 800, 2};
  cert3.contacts[1] = {4, 8, 8, 9, 800, 8};
  cert3.contacts[2] = {14, 15, 15, 19, 800, 15};
  cert3.nonzero_witness[0] = 9; cert3.nonzero_witness[1] = 19; cert3.nonzero_witness[2] = 1;
  cert3.B = BigRat(264825469, 200000000);

  std::vector<AxisCertificate> axes = {cert_hull, cert1, cert2, cert3};

  // Test coverage on the unit sphere
  int N = 200000;
  double min_cover = 1e9;
  vec3 worst_axis = {0,0,0};
  for (int i = 0; i < N; i++) {
    vec3 a = FibSphere(i, N);
    double max_margin = -1e9;
    for (int j = 0; j < 4; j++) {
      vec3 v = ComputeVariation(tri, axes[j], center);
      double dot = yocto::dot(a, v);
      if (dot > max_margin) max_margin = dot;
    }
    if (max_margin < min_cover) {
      min_cover = max_margin;
      worst_axis = a;
    }
  }

  std::cout << "Min coverage over sphere with 4 axes: " << min_cover << "\n";
  std::cout << "Worst axis: " << worst_axis.x << ", " << worst_axis.y << ", " << worst_axis.z << "\n";

  return 0;
}
