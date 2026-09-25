#include <iostream>
#include <vector>
#include <cmath>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  std::vector<ContactInfo> contacts;
  for (int mix : {0, 200, 333, 500, 666, 800, 1000}) {
    contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    contacts.push_back(MakeContact(19, 3, 3, 2, mix, 3));
    contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  std::cout << "Testing triples among " << contacts.size() << " contacts...\n";

  struct Axis {
    ContactInfo cont[3];
    vec3 c;
    BigVecQ3 cQ;
    BigRat delta;
    AxisCertificate cert;
  };

  std::vector<Axis> zero_defect_axes;
  std::string err;

  // Audit pairs and triples
  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo triple[3] = {contacts[i], contacts[j], contacts[k]};
        AxisCertificate ax;
        BigVecQ3 cQ;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &ax, &cQ, &delta, &err, BigRat(0))) {
          Axis a;
          a.cont[0] = contacts[i]; a.cont[1] = contacts[j]; a.cont[2] = contacts[k];
          a.c = {cQ.x.ToDouble(), cQ.y.ToDouble(), cQ.z.ToDouble()};
          a.cQ = cQ;
          a.delta = delta;
          a.cert = ax;
          zero_defect_axes.push_back(a);
        }
      }
    }
  }

  std::cout << "Found " << zero_defect_axes.size() << " zero-defect axes!\n";

  // Test whole-sphere coverage by all zero-defect axes
  int N = 50000;
  double min_all = 999.0;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 pt = {r * std::cos(phi), r * std::sin(phi), z};

    double m = -999.0;
    for (const auto &ax : zero_defect_axes) {
      double d = yocto::dot(pt, ax.c);
      if (d > m) m = d;
    }
    if (m < min_all) min_all = m;
  }
  std::cout << "Whole-sphere coverage of ALL " << zero_defect_axes.size() << " zero-defect axes: " << min_all << "\n";

  if (min_all > 0) {
    std::cout << "WHOLE SPHERE IS COVERED BY ZERO-DEFECT AXES!\n";
    std::cout << "Searching for a 4-axis cage...\n";
    // Search for 4-axis cage
    for (size_t i0 = 0; i0 < zero_defect_axes.size(); i0++) {
      for (size_t i1 = i0 + 1; i1 < zero_defect_axes.size(); i1++) {
        for (size_t i2 = i1 + 1; i2 < zero_defect_axes.size(); i2++) {
          for (size_t i3 = i2 + 1; i3 < zero_defect_axes.size(); i3++) {
            const vec3 &v0 = zero_defect_axes[i0].c;
            const vec3 &v1 = zero_defect_axes[i1].c;
            const vec3 &v2 = zero_defect_axes[i2].c;
            const vec3 &v3 = zero_defect_axes[i3].c;
            double min_c = 999.0;
            for (int s = 0; s < 500; s++) {
              double z = 1.0 - 2.0 * (s + 0.5) / 500;
              double r = std::sqrt(std::max(0.0, 1.0 - z * z));
              double phi = s * 2.399963229728653;
              vec3 pt = {r * std::cos(phi), r * std::sin(phi), z};
              double d = std::max({yocto::dot(pt, v0), yocto::dot(pt, v1), yocto::dot(pt, v2), yocto::dot(pt, v3)});
              if (d < min_c) min_c = d;
            }
            if (min_c > 0.001) {
              std::cout << "FOUND 4-AXIS ZERO DEFECT CAGE! inradius = " << min_c << "\n";
              std::cout << "Indices: " << i0 << ", " << i1 << ", " << i2 << ", " << i3 << "\n";
              return 0;
            }
          }
        }
      }
    }
  }

  return 0;
}
