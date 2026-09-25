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

  // Generate zero-defect candidate axes:
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
  std::vector<ContactInfo> axis_triples[3];
  std::vector<AxisCertificate> certs;
  std::vector<BigVecQ3> centers;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          certs.push_back(ax);
          centers.push_back(center / ax.B);
        }
      }
    }
  }

  std::cout << "Audited " << centers.size() << " zero-defect axes.\n";

  // Frank-Wolfe / Gilbert's algorithm to find closest point in conv(centers) to origin:
  // Start with any point:
  int N = centers.size();
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    pts[i] = {centers[i].x.ToDouble(), centers[i].y.ToDouble(), centers[i].z.ToDouble()};
  }

  // Current convex combination:
  vec3 p = pts[0];
  double best_dist = yocto::length(p);

  for (int step = 0; step < 200000; step++) {
    // Linear subproblem: find point minimizing dot(pts[i], p)
    int best_i = 0;
    double min_dot = yocto::dot(pts[0], p);
    for (int i = 1; i < N; i++) {
      double d = yocto::dot(pts[i], p);
      if (d < min_dot) {
        min_dot = d;
        best_i = i;
      }
    }

    // Duality gap:
    double gap = yocto::dot(p, p) - min_dot;
    if (gap < 1e-12 || min_dot > 0) {
      std::cout << "Terminated at step " << step << ": min_dot = " << min_dot
                << ", dist to origin = " << yocto::length(p) << "\n";
      if (min_dot > 0) {
        std::cout << "ORIGIN IS STRICTLY OUTSIDE! Separating hyperplane found with margin " << min_dot << "\n";
      } else {
        std::cout << "ORIGIN IS INSIDE! Distance = " << yocto::length(p) << "\n";
      }
      return 0;
    }

    // Line search between p and pts[best_i]:
    vec3 d = pts[best_i] - p;
    double gamma = -yocto::dot(p, d) / yocto::dot(d, d);
    gamma = std::max(0.0, std::min(1.0, gamma));
    p = p + d * gamma;
  }

  std::cout << "After 200000 steps: dist to origin = " << yocto::length(p) << "\n";
  return 0;
}
