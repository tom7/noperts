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

  // Precompute 2000 Fibonacci sphere points
  int N = 2000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  // Pick top 50 diverse axes
  std::vector<int> selected;
  std::vector<float> current_cover(N, -999.0f);
  for (int s = 0; s < 50; s++) {
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
    selected.push_back(best_axis);
    for (int i = 0; i < N; i++) {
      current_cover[i] = std::max(current_cover[i], (float)yocto::dot(pts[i], zero_defect_axes[best_axis].c));
    }
  }

  std::cout << "Testing 4-combinations among top 50...\n";
  int M = selected.size();
  for (int i0 = 0; i0 < M; i0++) {
    for (int i1 = i0 + 1; i1 < M; i1++) {
      for (int i2 = i1 + 1; i2 < M; i2++) {
        for (int i3 = i2 + 1; i3 < M; i3++) {
          const vec3 &v0 = zero_defect_axes[selected[i0]].c;
          const vec3 &v1 = zero_defect_axes[selected[i1]].c;
          const vec3 &v2 = zero_defect_axes[selected[i2]].c;
          const vec3 &v3 = zero_defect_axes[selected[i3]].c;

          // Compute barycentric coords of origin
          vec3 e1 = v1 - v0, e2 = v2 - v0, e3 = v3 - v0;
          double det = yocto::dot(e1, yocto::cross(e2, e3));
          if (std::abs(det) < 1e-9) continue;

          // solve sum_j b_j v_j = 0, sum b_j = 1
          // det3(v1, v2, v3) / det_tetra, etc.
          double d0 = -yocto::dot(v1, yocto::cross(v2, v3));
          double d1 =  yocto::dot(v0, yocto::cross(v2, v3));
          double d2 = -yocto::dot(v0, yocto::cross(v1, v3));
          double d3 =  yocto::dot(v0, yocto::cross(v1, v2));
          double d_tetra = d0 + d1 + d2 + d3;
          if (d_tetra == 0) continue;
          double b0 = d0 / d_tetra;
          double b1 = d1 / d_tetra;
          double b2 = d2 / d_tetra;
          double b3 = d3 / d_tetra;

          if (b0 > 0.05 && b1 > 0.05 && b2 > 0.05 && b3 > 0.05) {
            // Check sphere coverage
            double min_c = 999.0;
            for (int s = 0; s < N; s++) {
              double d = std::max({yocto::dot(pts[s], v0), yocto::dot(pts[s], v1), yocto::dot(pts[s], v2), yocto::dot(pts[s], v3)});
              if (d < min_c) min_c = d;
            }
            if (min_c > 0.001) {
              std::cout << "FOUND WELL-CENTERED 4-AXIS ZERO-DEFECT CAGE!\n";
              std::cout << "Origin barycentric coords: (" << b0 << ", " << b1 << ", " << b2 << ", " << b3 << ")\n";
              std::cout << "Sphere inradius: " << min_c << "\n";
              std::cout << "Selected indices: " << selected[i0] << ", " << selected[i1] << ", " << selected[i2] << ", " << selected[i3] << "\n";
              return 0;
            }
          }
        }
      }
    }
  }

  std::cout << "No well-centered 4-cage found among top 50.\n";
  return 0;
}
