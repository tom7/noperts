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

  // Generate all zero-defect candidate axes:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 200, 400, 500, 600, 800, 1000}) {
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
  std::vector<BigVecQ3> zero_defect_centers;
  std::vector<BigRat> zero_defect_Bs;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          zero_defect_centers.push_back(center / ax.B);
          zero_defect_Bs.push_back(ax.B);
        }
      }
    }
  }

  std::cout << "Audited " << zero_defect_centers.size() << " zero-defect axes.\n";

  // Check the convex hull of these centers: does 0 lie in the interior?
  // Quick test: is there a separating hyperplane from 0?
  // We want to find w in R^3 such that dot(w, v) > 0 for all v in zero_defect_centers.
  // We can use LP or random search / perceptron:
  std::vector<vec3> centers_f;
  centers_f.reserve(zero_defect_centers.size());
  for (const auto &c : zero_defect_centers) {
    centers_f.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
  }

  vec3 w = {1, 0, 0};
  int iterations = 100000;
  bool separated = false;
  for (int it = 0; it < iterations; it++) {
    double min_dot = 1e9;
    int worst_idx = -1;
    for (size_t i = 0; i < centers_f.size(); i++) {
      double d = yocto::dot(w, centers_f[i]);
      if (d < min_dot) {
        min_dot = d;
        worst_idx = i;
      }
    }
    if (min_dot > 1e-6) {
      separated = true;
      std::cout << "Separated! Hyperplane w = (" << w.x << ", " << w.y << ", " << w.z
                << ") has min_dot = " << min_dot << "\n";
      break;
    }
    // Perceptron step:
    w = yocto::normalize(w + centers_f[worst_idx] * 0.1);
  }

  if (!separated) {
    std::cout << "Perceptron did NOT find a separating hyperplane! 0 might be inside the convex hull!\n";
  } else {
    std::cout << "All zero-defect axes strictly lie on one side of a hyperplane! 0 is outside their convex hull.\n";
  }

  return 0;
}
