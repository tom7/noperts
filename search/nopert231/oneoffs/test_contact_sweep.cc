#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"
#include <iostream>
#include <iomanip>

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

static bool Bary4(const BigVecQ3 pts[4], const BigVecQ3 &target, BigRat lam[4]) {
  BigVecQ3 v0 = pts[0] - pts[3];
  BigVecQ3 v1 = pts[1] - pts[3];
  BigVecQ3 v2 = pts[2] - pts[3];
  BigVecQ3 w = target - pts[3];
  BigRat den = BigVecQ3::Det(v0, v1, v2);
  if (den == 0) return false;
  lam[0] = BigVecQ3::Det(w, v1, v2) / den;
  lam[1] = BigVecQ3::Det(v0, w, v2) / den;
  lam[2] = BigVecQ3::Det(v0, v1, w) / den;
  lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
  return true;
}

int main() {
  std::string path = "03121303021";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo sib_contacts[3][3] = {
    // Axis 1: sib1
    {MakeContact(15, 19, 19, 3, 200, 19), MakeContact(2, 1, 1, 4, 200, 1), MakeContact(8, 9, 9, 10, 200, 9)},
    // Axis 2: sib2
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15)},
    // Axis 3: cert_hull
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(10, 15, 15, 19, 800, 15)}
  };
  BigVecQ3 centers[4];
  for (int a = 0; a < 3; a++) {
    AxisCertificate ax;
    BigRat delta;
    std::string err;
    Tube229::AuditAxis(tri, sib_contacts[a], &ax, &centers[a + 1], &delta, &err);
  }

  // We want an axis whose center is roughly (-0.014, 0.018, -0.067).
  // In sib0:
  // Contact 0: MakeContact(3, 2, 2, 1, 800, 2)
  // Contact 1: MakeContact(1, 4, 4, 8, 800, 4)
  // Contact 2 was: MakeContact(13, 14, 14, 15, 200, 14)
  // Let's test varying mix of contact 2 from 0 to 1000 in steps of 20:
  for (int mix = 0; mix <= 1000; mix += 20) {
    ContactInfo c[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(13, 14, 14, 15, mix, 14)
    };
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    bool ok = Tube229::AuditAxis(tri, c, &ax, &center, &delta, &err);
    if (ok) {
      std::cout << "SUCCESS! mix=" << mix << " center=("
                << center.x.ToDouble() << ", " << center.y.ToDouble() << ", " << center.z.ToDouble() << ")\n";
    }
  }

  // Also test other candidate edges around 14, 15, 10:
  int edges[][4] = {
    {13, 14, 14, 15},
    {9, 10, 10, 15},
    {10, 15, 15, 19},
    {14, 15, 15, 19},
    {13, 14, 10, 15},
    {9, 10, 14, 15},
    {13, 17, 14, 15},
    {17, 14, 14, 15}
  };

  // Sweep mix 0 and mix 1 around 800 with Contact 2 on (10, 15, 15, 19, mix2, 15):
  for (int mix0 : {600, 700, 750, 800, 850, 900}) {
    for (int mix1 : {600, 700, 750, 800, 850, 900}) {
      for (int mix2 : {100, 200, 250, 300, 350, 400}) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, mix0, 2),
          MakeContact(1, 4, 4, 8, mix1, 4),
          MakeContact(10, 15, 15, 19, mix2, 15)
        };
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        bool ok = Tube229::AuditAxis(tri, c, &ax, &center, &delta, &err);
        if (ok) {
          BigVecQ3 test_tet[4] = {center, centers[1], centers[2], centers[3]};
          BigRat bary[4];
          BigVecQ3 origin(BigRat(0), BigRat(0), BigRat(0));
          if (Bary4(test_tet, origin, bary)) {
            if (bary[0] > 0 && bary[1] > 0 && bary[2] > 0 && bary[3] > 0) {
              BigRat r = Tube229::ExactTetrahedronAxisRadius(test_tet);
              std::cout << "STRICT CAGE FOUND! mix0=" << mix0 << " mix1=" << mix1 << " mix2=" << mix2
                        << " r_cage=" << r.ToDouble() << "\n";
              for (int i = 0; i < 4; i++) {
                std::cout << "  bary[" << i << "] = " << bary[i].ToDouble() << "\n";
              }
            }
          }
        }
      }
    }
  }

  return 0;
}
