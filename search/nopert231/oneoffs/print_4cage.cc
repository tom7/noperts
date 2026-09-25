#include <iostream>
#include <vector>
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

  // Precompute 2000 Fibonacci sphere points
  int N = 2000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  std::vector<int> selected_axes;
  std::vector<float> current_cover(N, -999.0f);
  for (int s = 0; s < 40; s++) {
    int worst_pt = 0;
    float min_val = 999.0f;
    for (int i = 0; i < N; i++) {
      if (current_cover[i] < min_val) {
        min_val = current_cover[i];
        worst_pt = i;
      }
    }
    int best_axis = -1;
    float best_gain = -999.0f;
    for (size_t a = 0; a < zero_defect_axes.size(); a++) {
      float d = (float)yocto::dot(pts[worst_pt], zero_defect_axes[a].c);
      if (d > best_gain) {
        best_gain = d;
        best_axis = a;
      }
    }
    selected_axes.push_back(best_axis);
    for (int i = 0; i < N; i++) {
      current_cover[i] = std::max(current_cover[i], (float)yocto::dot(pts[i], zero_defect_axes[best_axis].c));
    }
  }

  int pick[4] = {selected_axes[14], selected_axes[85], selected_axes[3433], selected_axes[12328]};
  // Wait! The indices reported were: 14, 85, 3433, 12328!
  // Wait, let's find the exact ones from find_exact_4cage:
  // In find_exact_4cage, the loop was:
  // for i0, i1, i2, i3 in 0..M (where M=40):
  // and printed: selected_axes[i0], ...
  // So the 4 axes are zero_defect_axes[14], zero_defect_axes[85], zero_defect_axes[3433], zero_defect_axes[12328]!
  
  std::cout << "Printing 4 axes:\n";
  int ax_idx[4] = {14, 85, 3433, 12328};
  BigRat max_delta(0);
  for (int m = 0; m < 4; m++) {
    const auto &ax = zero_defect_axes[ax_idx[m]];
    std::cout << "Axis " << m << ":\n";
    std::cout << "  c = (" << ax.cQ.x.ToString() << ", " << ax.cQ.y.ToString() << ", " << ax.cQ.z.ToString() << ")\n";
    std::cout << "  delta = " << ax.delta.ToString() << "\n";
    std::cout << "  B = " << ax.cert.B.ToString() << "\n";
    if (ax.delta > max_delta) max_delta = ax.delta;
  }
  std::cout << "Max delta = " << max_delta.ToString() << " (" << max_delta.ToDouble() << ")\n";

  return 0;
}
