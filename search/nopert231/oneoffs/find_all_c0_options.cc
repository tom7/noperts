#include <iostream>
#include <vector>
#include <algorithm>
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> fine_mixes;
  for (int m = 0; m <= 1000; m += 100) fine_mixes.push_back(m);

  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  std::cout << "Silhouette contacts generated: " << contacts.size() << "\n";

  ContactInfo c0 = MakeContact(3, 2, 2, 1, 800, 2);
  ContactInfo c1 = MakeContact(1, 4, 4, 8, 800, 4);

  double min_defect = 1.0;
  ContactInfo best_c2;

  for (const auto &c2 : contacts) {
    ContactInfo test_c[3] = {c0, c1, c2};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(1, 100))) {
      double lo = 0.0, hi = 0.01;
      for (int it = 0; it < 15; it++) {
        double mid = 0.5 * (lo + hi);
        if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat::FromDouble(mid))) {
          hi = mid;
        } else {
          lo = mid;
        }
      }
      if (hi < min_defect) {
        min_defect = hi;
        best_c2 = c2;
        std::cout << "New min defect: " << min_defect
                  << " with c2 = [" << c2.edge_start << "->" << c2.edge_finish
                  << ", " << c2.edge_start2 << "->" << c2.edge_finish2
                  << ", mix " << c2.mix << ", v " << c2.vertex << "]\n";
      }
    }
  }

  std::cout << "Overall min defect with c0, c1 fixed: " << min_defect << "\n";
  return 0;
}
