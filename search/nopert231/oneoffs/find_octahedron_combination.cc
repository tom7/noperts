#include <iostream>
#include <vector>
#include <array>
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

static BigRat det3(const BigVecQ3 &a, const BigVecQ3 &b, const BigVecQ3 &c) {
  return a.x * (b.y * c.z - b.z * c.y) -
         a.y * (b.x * c.z - b.z * c.x) +
         a.z * (b.x * c.y - b.y * c.x);
}

static BigRat tetraDet(const BigVecQ3 p[4]) {
  return -det3(p[1], p[2], p[3]) +
          det3(p[0], p[2], p[3]) -
          det3(p[0], p[1], p[3]) +
          det3(p[0], p[1], p[2]);
}

static bool SolveBarycentric(const BigVecQ3 p[4], const BigVecQ3 &target, BigRat out_b[4]) {
  BigRat d = tetraDet(p);
  if (d == BigRat(0)) return false;

  BigVecQ3 p1_t = p[1] - target;
  BigVecQ3 p2_t = p[2] - target;
  BigVecQ3 p3_t = p[3] - target;
  BigVecQ3 p0_t = p[0] - target;

  out_b[0] = -det3(p1_t, p2_t, p3_t) / d;
  out_b[1] =  det3(p0_t, p2_t, p3_t) / d;
  out_b[2] = -det3(p0_t, p1_t, p3_t) / d;
  out_b[3] =  det3(p0_t, p1_t, p2_t) / d;

  for (int j = 0; j < 4; j++) {
    if (out_b[j] < BigRat(0)) return false;
  }
  return true;
}

int main() {
  std::string target_path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target_path);

  // The 6 chosen axes from fast_greedy_cage:
  // Axis 14, 12329, 1183, 85, 3433, 12328
  // Let's audit them directly:
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
          a.cQ = cQ; a.delta = delta; a.cert = ax;
          zero_defect_axes.push_back(a);
        }
      }
    }
  }

  std::cout << "Audited " << zero_defect_axes.size() << " zero-defect axes.\n";

  int chosen_idx[6] = {14, 12329, 1183, 85, 3433, 12328};
  BigVecQ3 V[6];
  BigRat max_delta(0);
  for (int m = 0; m < 6; m++) {
    V[m] = zero_defect_axes[chosen_idx[m]].cQ;
    if (zero_defect_axes[chosen_idx[m]].delta > max_delta) {
      max_delta = zero_defect_axes[chosen_idx[m]].delta;
    }
  }
  std::cout << "Max delta = " << max_delta.ToDouble() << "\n";

  // Target octahedron with c = 1/5000:
  BigRat c(1, 5000);
  BigRat R = (c + max_delta) * BigRat(7, 4);

  BigVecQ3 targets[6] = {
    BigVecQ3(R, BigRat(0), BigRat(0)),
    BigVecQ3(-R, BigRat(0), BigRat(0)),
    BigVecQ3(BigRat(0), R, BigRat(0)),
    BigVecQ3(BigRat(0), -R, BigRat(0)),
    BigVecQ3(BigRat(0), BigRat(0), R),
    BigVecQ3(BigRat(0), BigRat(0), -R)
  };

  // For each target, check if it lies in any tetrahedron among the 6 vertices:
  bool all_covered = true;
  for (int t = 0; t < 6; t++) {
    bool found = false;
    for (int i0 = 0; i0 < 6 && !found; i0++) {
      for (int i1 = i0 + 1; i1 < 6 && !found; i1++) {
        for (int i2 = i1 + 1; i2 < 6 && !found; i2++) {
          for (int i3 = i2 + 1; i3 < 6 && !found; i3++) {
            BigVecQ3 p[4] = {V[i0], V[i1], V[i2], V[i3]};
            BigRat b[4];
            if (SolveBarycentric(p, targets[t], b)) {
              found = true;
              std::cout << "Target " << t << " is in tetrahedron {"
                        << i0 << ", " << i1 << ", " << i2 << ", " << i3 << "}!\n";
              std::cout << "  barycentric: " << b[0].ToDouble() << ", "
                        << b[1].ToDouble() << ", " << b[2].ToDouble() << ", "
                        << b[3].ToDouble() << "\n";
            }
          }
        }
      }
    }
    if (!found) {
      std::cout << "Target " << t << " NOT COVERED by any tetrahedron!\n";
      all_covered = false;
    }
  }

  if (all_covered) {
    std::cout << "ALL 6 OCTAHEDRON TARGETS ARE IN THE CONVEX HULL OF THE 6 AXES!\n";
    std::cout << "c = " << c.ToString() << " is a certified inradius!\n";
  }

  return 0;
}
