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

  std::cout << "Audited " << zero_defect_axes.size() << " zero-defect axes.\n";

  // Precompute Fibonacci sphere points
  int N = 20000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  // Precompute dot products: dots[axis_idx][pt_idx]
  std::vector<std::vector<float>> dots(zero_defect_axes.size(), std::vector<float>(N));
  for (size_t a = 0; a < zero_defect_axes.size(); a++) {
    for (int i = 0; i < N; i++) {
      dots[a][i] = (float)yocto::dot(pts[i], zero_defect_axes[a].c);
    }
  }

  std::vector<int> chosen;
  std::vector<float> current_cover(N, -999.0f);

  for (int step = 0; step < 10; step++) {
    // Find worst covered point
    int worst_pt = 0;
    float min_val = 999.0f;
    for (int i = 0; i < N; i++) {
      if (current_cover[i] < min_val) {
        min_val = current_cover[i];
        worst_pt = i;
      }
    }

    if (step > 0) {
      std::cout << "Step " << step << ": current min coverage = " << min_val << "\n";
      if (min_val > 0.0001f) {
        std::cout << "SUCCESS! Covered with " << step << " axes! Margin = " << min_val << "\n";
        break;
      }
    }

    // Pick axis that maximizes coverage on the worst point or overall
    int best_axis = -1;
    float best_gain = -999.0f;
    for (size_t a = 0; a < zero_defect_axes.size(); a++) {
      // Evaluate new min coverage if we add axis a
      float test_val = dots[a][worst_pt];
      if (test_val > best_gain) {
        best_gain = test_val;
        best_axis = a;
      }
    }

    chosen.push_back(best_axis);
    for (int i = 0; i < N; i++) {
      current_cover[i] = std::max(current_cover[i], dots[best_axis][i]);
    }
  }

  std::cout << "Chosen axes:\n";
  for (int idx : chosen) {
    const auto &ax = zero_defect_axes[idx];
    std::cout << "Axis " << idx << ": center = (" << ax.c.x << ", " << ax.c.y << ", " << ax.c.z << "), delta = " << ax.delta.ToDouble() << "\n";
  }

  return 0;
}
