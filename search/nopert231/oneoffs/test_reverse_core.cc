#include <iostream>
#include <vector>
#include <cmath>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));
  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  // Axis 496 had:
  // c[0]: start=2, finish=1, mix=200, v=1
  // c[1]: start=9, finish=10, mix=500, v=10
  // c[2]: start=3, finish=2, mix=800, v=2
  // and had unit_dot = -0.996726.

  // Let us try all vertex assignments for this contact topology,
  // both forward edges and reverse edges:
  std::vector<std::pair<int, int>> edges_fwd = {{2, 1}, {9, 10}, {3, 2}};
  std::vector<int> mixes = {200, 500, 800};

  for (bool rev : {false, true}) {
    for (int v0 = 0; v0 < 24; v0++) {
      for (int v1 = 0; v1 < 24; v1++) {
        for (int v2 = 0; v2 < 24; v2++) {
          ContactInfo c[3];
          for (int m = 0; m < 3; m++) {
            int s = edges_fwd[m].first;
            int f = edges_fwd[m].second;
            int v = (m == 0 ? v0 : m == 1 ? v1 : v2);
            if (!rev) {
              c[m] = MakeContact(s, f, s, f, mixes[m], v);
            } else {
              c[m] = MakeContact(f, s, f, s, 1000 - mixes[m], v);
            }
          }
          AxisCertificate ax;
          BigVecQ3 ctr;
          BigRat del;
          if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0))) {
            vec3 uc = {ctr.x.ToDouble() / ax.B.ToDouble(),
                       ctr.y.ToDouble() / ax.B.ToDouble(),
                       ctr.z.ToDouble() / ax.B.ToDouble()};
            double dot = yocto::dot(u0_dir, yocto::normalize(uc));
            double ang = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
            std::cout << "AUDIT SUCCESS! rev=" << rev << ", v=(" << v0 << "," << v1 << "," << v2
                      << "), del=" << del.ToDouble() << ", dot=" << dot << ", ang=" << ang << " deg\n";
            if (dot > 0.9) {
              std::cout << "FOUND ALIGNED ZERO-DEFECT AXIS!\n";
              return 0;
            }
          }
        }
      }
    }
  }

  std::cout << "Done search.\n";
  return 0;
}
