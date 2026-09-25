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
  double px = 0.902448, py = -0.902448;

  double max_dot = -1e9;
  int best_cand = -1;
  for (size_t i = 0; i < cands.size(); i++) {
    vec3 v = cands[i].normalized_a;
    double d = yocto::dot(u0, v) + px * yocto::dot(e1, v) + py * yocto::dot(e2, v);
    if (d > max_dot) {
      max_dot = d;
      best_cand = i;
    }
  }

  std::cout << "At (" << px << ", " << py << "): max dot = " << max_dot << " on cand " << best_cand << "\n";
  return 0;
}
