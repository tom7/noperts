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

  // Annular axis u0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  double min_ang = 1e9;
  ContactInfo best_c[3];
  vec3 best_v;
  BigRat best_del;

  // Let's test pairs of edges at vertex 2, vertex 4, and vertex 15:
  std::vector<std::pair<int, int>> e2 = {{3, 2}, {2, 1}, {2, 5}};
  std::vector<std::pair<int, int>> e4 = {{2, 1}, {1, 4}, {4, 8}};
  std::vector<std::pair<int, int>> e15 = {{10, 15}, {13, 14}, {14, 15}, {15, 19}};

  for (int mix0 : {600, 700, 800, 900, 1000}) {
    for (int mix1 : {600, 700, 800, 900, 1000}) {
      for (const auto &p15 : e15) {
        for (const auto &p15_2 : e15) {
          if (p15 == p15_2) continue;
          for (int mix2 = 0; mix2 <= 1000; mix2 += 50) {
            ContactInfo cand[3] = {
              MakeContact(3, 2, 2, 1, mix0, 2),
              MakeContact(1, 4, 4, 8, mix1, 4),
              MakeContact(p15.first, p15.second, p15_2.first, p15_2.second, mix2, 15)
            };
            AxisCertificate ax;
            BigVecQ3 ctr;
            BigRat del;
            if (Tube229::AuditAxis(tri, cand, &ax, &ctr, &del, &err, BigRat(0))) {
              vec3 v = {ctr.x.ToDouble() / ax.B.ToDouble(),
                        ctr.y.ToDouble() / ax.B.ToDouble(),
                        ctr.z.ToDouble() / ax.B.ToDouble()};
              double ang = std::acos(std::max(-1.0, std::min(1.0, (double)yocto::dot(u0_dir, yocto::normalize(v))))) * 180.0 / M_PI;
              if (ang < min_ang) {
                min_ang = ang;
                best_c[0] = cand[0]; best_c[1] = cand[1]; best_c[2] = cand[2];
                best_v = v;
                best_del = del;
                std::cout << "New min angle: " << min_ang << " deg (del = " << del.ToDouble() << ")\n";
                std::cout << "  mix0=" << mix0 << ", mix1=" << mix1 << ", e15=("
                          << p15.first << "->" << p15.second << ", " << p15_2.first << "->" << p15_2.second << ") mix=" << mix2 << "\n";
              }
            }
          }
        }
      }
    }
  }

  std::cout << "FINAL MIN ANGLE: " << min_ang << " degrees\n";
  return 0;
}
