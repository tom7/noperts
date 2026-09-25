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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 dir0 = yocto::normalize(u0);

  double best_dot = -1.0;
  ContactInfo best_c[3];

  // Try all possible contacts for c2
  for (int s = 0; s < 20; s++) {
    for (int f = 0; f < 20; f++) {
      if (s == f) continue;
      // check if edge exists
      bool edge1 = false;
      for (int nb : Tube229::Neighbors(s)) if (nb == f) edge1 = true;
      if (!edge1) continue;

      for (int f2 = 0; f2 < 20; f2++) {
        if (f2 == f || f2 == s) continue;
        bool edge2 = false;
        for (int nb : Tube229::Neighbors(f)) if (nb == f2) edge2 = true;
        if (!edge2) continue;

        for (int mix : {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000}) {
          for (int v : {s, f, f2}) {
            ContactInfo c2 = MakeContact(s, f, f, f2, mix, v);
            ContactInfo test_c[3] = {c_ann[0], c_ann[1], c2};
            AxisCertificate ax; BigVecQ3 ctr; BigRat del;
            if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
              vec3 u = {ctr.x.ToDouble() / ax.B.ToDouble(),
                        ctr.y.ToDouble() / ax.B.ToDouble(),
                        ctr.z.ToDouble() / ax.B.ToDouble()};
              double dot = yocto::dot(yocto::normalize(u), dir0);
              if (dot > best_dot) {
                best_dot = dot;
                double ang = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
                std::cout << "New best zero-defect axis: dot = " << dot
                          << " (angle = " << ang << " deg), c2 = ("
                          << s << "->" << f << "->" << f2 << ", mix " << mix << ", v " << v << ")\n";
              }
            }
          }
        }
      }
    }
  }
  return 0;
}
