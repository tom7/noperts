#include <iostream>
#include <vector>
#include <cmath>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  // The 9 vertices on the true hull cycle:
  // e.g. 1, 2, 3, 4, 8, 9, 10, 15, 19
  // Let us get all candidate contacts from the hull edges
  // Contact pairs:
  // v1: (2->1)/(1->4)
  // v2: (3->2)/(2->1)
  // v3: (19->3)/(3->2)
  // v4: (1->4)/(4->8)
  // v8: (4->8)/(8->9)
  // v9: (8->9)/(9->10)
  // v10: (9->10)/(10->15)
  // v15: (10->15)/(15->19)
  // v19: (15->19)/(19->3)
  std::vector<ContactInfo> hull_contacts = {
    MakeContact(2, 1, 1, 4, 500, 1),
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(19, 3, 3, 2, 500, 3),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(4, 8, 8, 9, 500, 8),
    MakeContact(8, 9, 9, 10, 500, 9),
    MakeContact(9, 10, 10, 15, 500, 10),
    MakeContact(10, 15, 15, 19, 800, 15),
    MakeContact(15, 19, 19, 3, 500, 19)
  };

  std::vector<vec3> audited_axes;
  std::string err;

  for (size_t i = 0; i < hull_contacts.size(); i++) {
    for (size_t j = i + 1; j < hull_contacts.size(); j++) {
      for (size_t k = j + 1; k < hull_contacts.size(); k++) {
        ContactInfo triple[3] = {hull_contacts[i], hull_contacts[j], hull_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 c;
        BigRat d;
        if (Tube229::AuditAxis(tri, triple, &ax, &c, &d, &err, BigRat(0))) {
          audited_axes.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
        }
      }
    }
  }

  std::cout << "Found " << audited_axes.size() << " audited zero-defect multi-vertex hull axes!\n";

  // Add the 3 standard complement axes u1, u2, u3
  ContactInfo cont1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo cont2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo cont3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  for (auto *c : {cont1, cont2, cont3}) {
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat d;
    if (Tube229::AuditAxis(tri, c, &ax, &center, &d, &err, BigRat(0))) {
      audited_axes.push_back({center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
    }
  }

  // Now test sphere coverage
  int N = 100000;
  double min_cover = 999.0;
  vec3 worst_pt = {0, 0, 0};
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    double m = -999.0;
    for (const auto &u : audited_axes) {
      double d = yocto::dot(a, u);
      if (d > m) m = d;
    }
    if (m < min_cover) {
      min_cover = m;
      worst_pt = a;
    }
  }

  std::cout << "WHOLE SPHERE COVERAGE WITH ALL ZERO-DEFECT AXES: " << min_cover << "\n";
  std::cout << "Worst point: (" << worst_pt.x << ", " << worst_pt.y << ", " << worst_pt.z << ")\n";
  return 0;

}
