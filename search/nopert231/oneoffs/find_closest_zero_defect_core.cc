#include <iostream>
#include <vector>
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

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  // We want to find an axis with ZERO defect on tri that is closest to u0.
  // Axis 0 contacts:
  // c[0]: 3->2, 2->1, v=2
  // c[1]: 1->4, 4->8, v=4
  // c[2]: 13->14, 14->15, v=14
  // u0 direction:
  vec3 u0 = {-0.01389, 0.01857, -0.06689};
  vec3 u0_hat = yocto::normalize(u0);

  // Let's test a dense grid of contacts near Axis 0:
  // Contact 0 variants: around v=2, 3, 1
  // Contact 1 variants: around v=4, 8, 1
  // Contact 2 variants: around v=14, 15, 13, 19
  struct ContactChoice {
    int s1, f1, s2, f2, v;
  };
  std::vector<ContactChoice> c0_choices = {
    {3, 2, 2, 1, 2},
    {19, 3, 3, 2, 3},
    {2, 1, 1, 4, 1}
  };
  std::vector<ContactChoice> c1_choices = {
    {1, 4, 4, 8, 4},
    {4, 8, 8, 9, 8},
    {2, 1, 1, 4, 1}
  };
  std::vector<ContactChoice> c2_choices = {
    {13, 14, 14, 15, 14},
    {14, 15, 15, 19, 15},
    {10, 15, 15, 19, 15},
    {15, 19, 19, 3, 19}
  };

  struct Winner {
    double deg;
    double dot;
    ContactInfo c[3];
  };
  std::vector<Winner> winners;

  for (const auto &ch0 : c0_choices) {
    for (const auto &ch1 : c1_choices) {
      for (const auto &ch2 : c2_choices) {
        for (int m0 = 0; m0 <= 1000; m0 += 200) {
          for (int m1 = 0; m1 <= 1000; m1 += 200) {
            for (int m2 = 0; m2 <= 1000; m2 += 200) {
              ContactInfo c[3] = {
                MakeContact(ch0.s1, ch0.f1, ch0.s2, ch0.f2, m0, ch0.v),
                MakeContact(ch1.s1, ch1.f1, ch1.s2, ch1.f2, m1, ch1.v),
                MakeContact(ch2.s1, ch2.f1, ch2.s2, ch2.f2, m2, ch2.v)
              };
              AxisCertificate ax;
              BigVecQ3 ctr;
              BigRat del;
              std::string err;
              if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0))) {
                vec3 a = yocto::normalize(ToDouble(ctr));
                double d = yocto::dot(a, u0_hat);
                double deg = acos(std::min(1.0, std::max(-1.0, d))) * 180.0 / M_PI;
                winners.push_back({deg, d, {c[0], c[1], c[2]}});
              }
            }
          }
        }
      }
    }
  }

  std::sort(winners.begin(), winners.end(), [](const Winner &x, const Winner &y) {
    return x.deg < y.deg;
  });

  std::cout << "Found " << winners.size() << " zero-defect axes!\n";
  for (size_t i = 0; i < std::min((size_t)10, winners.size()); i++) {
    std::cout << "Winner " << i << ": deg = " << winners[i].deg << " (dot = " << winners[i].dot << ")\n";
    for (int m = 0; m < 3; m++) {
      std::cout << "  c[" << m << "]: " << winners[i].c[m].edge_start << "->" << winners[i].c[m].edge_finish
                << " mix=" << winners[i].c[m].mix << " v=" << winners[i].c[m].vertex << "\n";
    }
  }
  return 0;
}
