#include <iostream>
#include <vector>
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

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 centroid = vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  };

  auto cands = Tube229::GenerateCandidatesForView(centroid, tri, true, 4, true, 1e-12);
  vec3 vA = cands[12106].normalized_a;
  vec3 vB = cands[12430].normalized_a;

  // Segment from V0 to V1:
  double x0 = 0.673022, y0 = -0.673022;
  double x1 = 1.34604,  y1 = -1.34604;

  auto eval = [&](vec3 v, double x, double y) {
    return yocto::dot(u0, v) + x * yocto::dot(e1, v) + y * yocto::dot(e2, v);
  };

  double fA0 = eval(vA, x0, y0), fA1 = eval(vA, x1, y1);
  double fB0 = eval(vB, x0, y0), fB1 = eval(vB, x1, y1);

  std::cout << "At V0: fA = " << fA0 << ", fB = " << fB0 << "\n";
  std::cout << "At V1: fA = " << fA1 << ", fB = " << fB1 << "\n";

  // Intersection along segment: fA(t) = fB(t)
  // (fA0 + t*(fA1 - fA0)) = (fB0 + t*(fB1 - fB0))
  // t * ((fA1 - fA0) - (fB1 - fB0)) = fB0 - fA0
  double t = (fB0 - fA0) / ((fA1 - fA0) - (fB1 - fB0));
  std::cout << "Intersection parameter t = " << t << "\n";
  double xi = x0 + t * (x1 - x0);
  double yi = y0 + t * (y1 - y0);
  std::cout << "Intersection point: (" << xi << ", " << yi << ")\n";
  std::cout << "Value at intersection: fA = " << eval(vA, xi, yi) << ", fB = " << eval(vB, xi, yi) << "\n";

  return 0;
}
