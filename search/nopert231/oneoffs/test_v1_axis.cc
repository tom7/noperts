#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

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

  std::cout << "Auditing axis with contacts on v2, v4, v1...\n";
  for (int m0 : {0, 200, 500, 800, 1000}) {
    for (int m1 : {0, 200, 500, 800, 1000}) {
      for (int m2 : {0, 200, 500, 800, 1000}) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(2, 1, 1, 4, m2, 1)
        };
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, c, &ax, &center, &delta, &err, BigRat(1, 100))) {
          std::cout << "AUDIT SUCCESS! m0=" << m0 << " m1=" << m1 << " m2=" << m2
                    << " B=" << ax.B.ToDouble() << " delta=" << delta.ToDouble()
                    << " center=(" << center.x.ToDouble() << ", " << center.y.ToDouble() << ", " << center.z.ToDouble() << ")\n";
          return 0;
        } else if (m0 == 0 && m1 == 0 && m2 == 0) {
          std::cout << "m=(0,0,0) err: " << err << "\n";
        }
      }
    }
  }

  std::cout << "Audit failed for all tested mixes.\n";
  return 0;
}
