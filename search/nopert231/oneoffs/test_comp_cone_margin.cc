#include <iostream>
#include <cmath>
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
  std::string target = "03121303022";
  TriangleQ tri = TriangleFromPath(target);

  // 4 axes from test_all_canyon_leaves.cc:
  ContactInfo cont0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo cont1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo cont2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo cont3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15) // Axis 3 is the true hull axis!
  };

  ContactInfo *conts[4] = {cont0, cont1, cont2, cont3};
  AxisCertificate ax[4];
  BigVecQ3 centers[4];
  BigRat deltas[4];
  std::string err;

  for (int a = 0; a < 4; a++) {
    Tube229::AuditAxis(tri, conts[a], &ax[a], &centers[a], &deltas[a], &err, a == 0 ? BigRat(5, 1000) : BigRat(0));
  }

  vec3 u0 = {centers[0].x.ToDouble(), centers[0].y.ToDouble(), centers[0].z.ToDouble()};
  vec3 u1 = {centers[1].x.ToDouble(), centers[1].y.ToDouble(), centers[1].z.ToDouble()};
  vec3 u2 = {centers[2].x.ToDouble(), centers[2].y.ToDouble(), centers[2].z.ToDouble()};
  vec3 u3 = {centers[3].x.ToDouble(), centers[3].y.ToDouble(), centers[3].z.ToDouble()};

  double c_cone = 0.060;
  double min_cover = 999.0;
  vec3 worst_a = {0, 0, 0};
  double worst_dot0 = 0;

  // Dense sphere sampling (1,000,000 points)
  int N = 1000000;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653; // golden angle
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    double dot0 = yocto::dot(a, u0);
    if (dot0 >= c_cone) continue; // inside exceptional cone

    double max_comp = std::max(yocto::dot(a, u1), std::max(yocto::dot(a, u2), yocto::dot(a, u3)));
    if (max_comp < min_cover) {
      min_cover = max_comp;
      worst_a = a;
      worst_dot0 = dot0;
    }
  }

  std::cout << "Outside cone (dot0 < " << c_cone << "):\n"
            << "  min complement coverage across 1M points = " << min_cover << "\n"
            << "  worst a = (" << worst_a.x << ", " << worst_a.y << ", " << worst_a.z << ")\n"
            << "  worst dot0 = " << worst_dot0 << " (angle with u0 = "
            << std::acos(worst_dot0 / yocto::length(u0)) * 180.0 / M_PI << " deg)\n"
            << "  delta_max = " << std::max(deltas[1].ToDouble(), std::max(deltas[2].ToDouble(), deltas[3].ToDouble())) << "\n"
            << "  net margin = " << min_cover - deltas[1].ToDouble() << "\n";

  return 0;
}
