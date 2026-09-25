#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::vector<std::string> nodes = {
    "03121300",
    "0312130332",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200"
  };

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  for (const auto &path : nodes) {
    TriangleQ tri = TriangleFromPath(path);
    AxisCertificate ann_cert;
    BigVecQ3 ann_center;
    BigRat ann_del;
    std::string err;
    bool ok = Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(5, 1000));
    std::cout << "Node " << path << ":\n";
    if (!ok) {
      std::cout << "  Annular audit failed: " << err << "\n";
      continue;
    }
    double B0 = ann_cert.B.ToDouble();
    vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
    std::cout << "  Annular delta = " << ann_del.ToDouble() << ", B = " << B0 << "\n";
    std::cout << "  u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";

    // View triangle corners:
    auto c0 = tri.corners[0];
    auto c1 = tri.corners[1];
    auto c2 = tri.corners[2];
    vec3 v0 = vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};
    vec3 v1 = vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()};
    vec3 v2 = vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()};
    vec3 centroid = (v0 + v1 + v2) / 3.0;
    std::cout << "  Centroid: (" << centroid.x << ", " << centroid.y << ", " << centroid.z << ")\n";
    std::cout << "  Dot(u0, centroid) = " << yocto::dot(u0, yocto::normalize(centroid)) << "\n";

    // Sample candidates:
    auto cands = Tube229::GenerateCandidatesForView(centroid, tri, false, 0, false, 1e-12);
    int zero_count = 0;
    for (const auto &c : cands) {
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      ContactInfo contacts[3] = {c.contacts[0], c.contacts[1], c.contacts[2]};
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        zero_count++;
      }
    }
    std::cout << "  Candidates: " << cands.size() << ", audited zero-defect: " << zero_count << "\n";
  }

  return 0;
}
