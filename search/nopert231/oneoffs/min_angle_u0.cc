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

  // Axis 0:
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
  vec3 u0_dir = yocto::normalize(u0);

  // Generate all zero-defect candidate axes:
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
  double min_angle = 1e9;
  ContactInfo best_triple[3];
  vec3 best_v;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          vec3 v = {center.x.ToDouble() / ax.B.ToDouble(),
                    center.y.ToDouble() / ax.B.ToDouble(),
                    center.z.ToDouble() / ax.B.ToDouble()};
          double ang = std::acos(std::max(-1.0, std::min(1.0, (double)yocto::dot(u0_dir, yocto::normalize(v))))) * 180.0 / M_PI;
          if (ang < min_angle) {
            min_angle = ang;
            best_triple[0] = triple[0];
            best_triple[1] = triple[1];
            best_triple[2] = triple[2];
            best_v = v;
          }
        }
      }
    }
  }

  std::cout << "Minimum angle between u0 and ANY zero-defect axis: " << min_angle << " degrees\n";
  std::cout << "Best axis center: (" << best_v.x << ", " << best_v.y << ", " << best_v.z << ")\n";
  for (int m = 0; m < 3; m++) {
    std::cout << "  Contact " << m << ": edges ("
              << best_triple[m].edge_start << "->" << best_triple[m].edge_finish
              << ", " << best_triple[m].edge_start2 << "->" << best_triple[m].edge_finish2
              << ") mix=" << best_triple[m].mix << " v=" << best_triple[m].vertex << "\n";
  }

  return 0;
}
