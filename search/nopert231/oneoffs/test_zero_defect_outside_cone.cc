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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Annular axis u0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  // Generate candidates across all contact mixes:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    cand_contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  int C = cand_contacts.size();
  std::vector<vec3> zero_defect_dirs;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          zero_defect_dirs.push_back({center.x.ToDouble() / ax.B.ToDouble(),
                                     center.y.ToDouble() / ax.B.ToDouble(),
                                     center.z.ToDouble() / ax.B.ToDouble()});
        }
      }
    }
  }

  std::cout << "Audited " << zero_defect_dirs.size() << " zero-defect axes.\n";

  // Test coverage outside cone: dot(a, u0) < c_cone
  for (double c_cone : {0.020, 0.025, 0.030, 0.035, 0.040}) {
    double min_cover = 1e9;
    int N = 200000;
    vec3 worst_a = {0, 0, 0};
    int pts = 0;
    for (int i = 0; i < N; i++) {
      double z = 1.0 - (2.0 * i + 1.0) / N;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi = i * 2.399963229728653;
      vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
      if (yocto::dot(a, u0) < c_cone) {
        pts++;
        double max_d = -1e9;
        for (const auto &zd : zero_defect_dirs) {
          double d = yocto::dot(a, zd);
          if (d > max_d) max_d = d;
        }
        if (max_d < min_cover) {
          min_cover = max_d;
          worst_a = a;
        }
      }
    }
    std::cout << "Outside c_cone = " << c_cone << " (" << pts << " pts): min cover = "
              << min_cover << ", worst dot(a, u0) = " << yocto::dot(worst_a, u0) << "\n";
  }

  return 0;
}
