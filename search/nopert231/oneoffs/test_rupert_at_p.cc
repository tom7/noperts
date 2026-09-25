#include <iostream>
#include <vector>
#include "nopert229.h"
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double x = 1.26511, y = -0.969618;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  std::cout << "Direction p: (" << p.x << ", " << p.y << ", " << p.z << ")\n";

  // Check the view triangle centroid:
  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 centroid = vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  };
  std::cout << "View direction centroid: (" << centroid.x << ", " << centroid.y << ", " << centroid.z << ")\n";
  std::cout << "Dot(p, centroid) = " << yocto::dot(p, centroid) << "\n";
  std::cout << "Dot(p, u0) = " << yocto::dot(p, u0) << "\n";

  // Compute 2D convex hull of Noperthedron projected along centroid:
  // Is the adversary pose (rotated around p by some angle theta) able to fit?
  // Let's test a sweep of rotation angles theta around p:
  // For each theta, what is the clearance?
  for (double angle_deg = 0.0; angle_deg <= 180.0; angle_deg += 5.0) {
    double th = angle_deg * M_PI / 180.0;
    // Rotation matrix around p by angle th:
    // Check clearance...
  }

  return 0;
}
