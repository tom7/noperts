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

  struct Axis {
    vec3 c;
    BigVecQ3 cQ;
    BigRat delta;
  };
  std::vector<Axis> zero_axes;
  std::string err;

  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo triple[3] = {contacts[i], contacts[j], contacts[k]};
        AxisCertificate ax;
        BigVecQ3 cQ;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &ax, &cQ, &delta, &err, BigRat(0))) {
          Axis a;
          a.c = {cQ.x.ToDouble(), cQ.y.ToDouble(), cQ.z.ToDouble()};
          a.cQ = cQ;
          a.delta = delta;
          zero_axes.push_back(a);
        }
      }
    }
  }

  // Precompute 1000 points on sphere
  int N = 1000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  // Greedily find 5 axes that maximize minimum coverage on the sphere:
  std::vector<int> chosen;
  std::vector<double> current_cov(N, -999.0);

  for (int step = 0; step < 5; step++) {
    int best_ax = -1;
    double best_min = -999.0;
    for (size_t a = 0; a < zero_axes.size(); a++) {
      double min_c = 999.0;
      for (int p = 0; p < N; p++) {
        double d = std::max(current_cov[p], (double)yocto::dot(pts[p], zero_axes[a].c));
        if (d < min_c) min_c = d;
      }
      if (min_c > best_min) {
        best_min = min_c;
        best_ax = a;
      }
    }
    chosen.push_back(best_ax);
    for (int p = 0; p < N; p++) {
      current_cov[p] = std::max(current_cov[p], (double)yocto::dot(pts[p], zero_axes[best_ax].c));
    }
    std::cout << "Step " << step + 1 << ": best min coverage = " << best_min << "\n";
  }

  return 0;
}
