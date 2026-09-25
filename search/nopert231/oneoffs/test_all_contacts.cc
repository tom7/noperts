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

  vec3 a = yocto::normalize(vec3{0.306184, -0.727484, -0.614018});

  // Collect candidate contacts from true hull:
  // Hull vertices: 1, 2, 4, 8, 9, 10, 14, 15, 19
  // Candidate edges:
  // (3->2, 2->1), (1->4, 4->8), (4->8, 8->9), (8->9, 9->10),
  // (9->10, 10->15), (10->15, 15->19), (14->15, 15->19), (13->14, 14->15)
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {200, 400, 500, 600, 800}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
  }

  std::cout << "Testing " << cand_contacts.size() << " candidate contacts ("
            << (cand_contacts.size() * (cand_contacts.size() - 1) * (cand_contacts.size() - 2) / 6)
            << " triples)...\n";

  int zero_defect_count = 0;
  double best_dot = -1e9;
  ContactInfo best_triple[3];
  AxisCertificate best_ax;

  int C = cand_contacts.size();
  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          zero_defect_count++;
          vec3 v = {center.x.ToDouble() / ax.B.ToDouble(),
                    center.y.ToDouble() / ax.B.ToDouble(),
                    center.z.ToDouble() / ax.B.ToDouble()};
          double d = yocto::dot(a, v);
          if (d > best_dot) {
            best_dot = d;
            best_triple[0] = triple[0];
            best_triple[1] = triple[1];
            best_triple[2] = triple[2];
            best_ax = ax;
          }
        }
      }
    }
  }

  std::cout << "Found " << zero_defect_count << " zero-defect axes.\n";
  std::cout << "Best dot with fail point a: " << best_dot << "\n";
  if (best_dot > 0) {
    std::cout << "SUCCESS! A zero-defect axis covers the fail point with dot = " << best_dot << "!\n";
    for (int m = 0; m < 3; m++) {
      std::cout << "  Contact " << m << ": edges ("
                << best_triple[m].edge_start << "->" << best_triple[m].edge_finish
                << ", " << best_triple[m].edge_start2 << "->" << best_triple[m].edge_finish2
                << ") mix=" << best_triple[m].mix << " v=" << best_triple[m].vertex << "\n";
    }
  }

  return 0;
}
