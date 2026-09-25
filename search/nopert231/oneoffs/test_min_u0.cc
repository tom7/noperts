#include <iostream>
#include <string>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  std::string err;
  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 ctr0, ctr1, ctr2, ctr3;
  BigRat del0, del1, del2, del3;

  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(), ctr1.y.ToDouble() / ax1.B.ToDouble(), ctr1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 u2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(), ctr2.y.ToDouble() / ax2.B.ToDouble(), ctr2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 u3 = {ctr3.x.ToDouble() / ax3.B.ToDouble(), ctr3.y.ToDouble() / ax3.B.ToDouble(), ctr3.z.ToDouble() / ax3.B.ToDouble()};

  double c_comp = 0.001;
  double min_dot_u0 = 1e30;
  int count_satisfying = 0;

  // Sample 2,000,000 points on S^2:
  int N = 2000000;
  double golden_ratio = (1.0 + std::sqrt(5.0)) / 2.0;
  for (int i = 0; i < N; i++) {
    double theta = 2.0 * M_PI * i / golden_ratio;
    double phi = std::acos(1.0 - 2.0 * (i + 0.5) / N);
    vec3 a = {std::cos(theta) * std::sin(phi), std::sin(theta) * std::sin(phi), std::cos(phi)};

    if (yocto::dot(a, u1) <= c_comp &&
        yocto::dot(a, u2) <= c_comp &&
        yocto::dot(a, u3) <= c_comp) {
      count_satisfying++;
      double d0 = yocto::dot(a, u0);
      if (d0 < min_dot_u0) {
        min_dot_u0 = d0;
      }
    }
  }

  std::cout << "Tested " << N << " points on S^2.\n";
  std::cout << "Points with max(a.u1, a.u2, a.u3) <= " << c_comp << ": " << count_satisfying << "\n";
  std::cout << "Minimum of a . u0 among these points: " << min_dot_u0 << "\n";

  return 0;
}
