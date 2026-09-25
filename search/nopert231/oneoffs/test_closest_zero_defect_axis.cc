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
  vec3 u0 = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};
  vec3 u0_norm = u0 / yocto::length(u0);

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
  double min_angle_deg = 180.0;
  ContactInfo best_triple[3];

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          vec3 v = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
          double cos_th = yocto::dot(u0_norm, v / yocto::length(v));
          double angle = std::acos(std::max(-1.0, std::min(1.0, cos_th))) * 180.0 / M_PI;
          if (angle < min_angle_deg) {
            min_angle_deg = angle;
            best_triple[0] = triple[0]; best_triple[1] = triple[1]; best_triple[2] = triple[2];
          }
        }
      }
    }
  }

  std::cout << "Closest zero-defect axis to u0 has angle: " << min_angle_deg << " degrees!\n";
  return 0;
}
