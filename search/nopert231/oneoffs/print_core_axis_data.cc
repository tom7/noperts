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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 100000000));
  vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  vec3 u0_hat = yocto::normalize(u0);

  std::vector<ContactInfo> contacts;
  for (int mix : {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000}) {
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

  double max_dot = -1.0;
  ContactInfo best_triple[3];
  BigVecQ3 best_ctr;
  BigRat best_del;
  AxisCertificate best_cert;

  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo triple[3] = {contacts[i], contacts[j], contacts[k]};
        AxisCertificate ax;
        BigVecQ3 cQ;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &ax, &cQ, &delta, &err, BigRat(0))) {
          vec3 v = {cQ.x.ToDouble(), cQ.y.ToDouble(), cQ.z.ToDouble()};
          double dot = yocto::dot(u0_hat, yocto::normalize(v));
          if (dot > max_dot) {
            max_dot = dot;
            best_triple[0] = contacts[i];
            best_triple[1] = contacts[j];
            best_triple[2] = contacts[k];
            best_ctr = cQ;
            best_del = delta;
            best_cert = ax;
          }
        }
      }
    }
  }

  std::cout << "Inner Core Axis: dot = " << max_dot << ", delta = " << best_del.ToString() << "\n";
  std::cout << "Center = (" << best_ctr.x.ToString() << ", " << best_ctr.y.ToString() << ", " << best_ctr.z.ToString() << ")\n";
  for (int c = 0; c < 3; c++) {
    std::cout << "  contact " << c << ": ("
              << best_triple[c].edge_start << "->" << best_triple[c].edge_finish
              << ", " << best_triple[c].edge_start2 << "->" << best_triple[c].edge_finish2
              << ", mix " << best_triple[c].mix << ", v " << best_triple[c].vertex << ")\n";
  }

  return 0;
}
