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

  // 4 axes from tree_0.json:
  // Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  // Comp 0:
  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  // Comp 1:
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  // Comp 2:
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  ContactInfo *contacts[4] = {c0, c1, c2, c3};
  vec3 u[4];
  for (int a = 0; a < 4; a++) {
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    Tube229::AuditAxis(tri, contacts[a], &ax, &center, &delta, &err, (a == 0) ? BigRat(5, 1000) : BigRat(0));
    u[a] = {center.x.ToDouble() / ax.B.ToDouble(),
            center.y.ToDouble() / ax.B.ToDouble(),
            center.z.ToDouble() / ax.B.ToDouble()};
    std::cout << "u[" << a << "]: (" << u[a].x << ", " << u[a].y << ", " << u[a].z << ") len=" << yocto::length(u[a]) << "\n";
  }

  // Core axis:
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  std::string err;
  Tube229::AuditAxis(tri, c_core, &ax_core, &center_core, &delta_core, &err, BigRat(0));
  vec3 v_core = {center_core.x.ToDouble() / ax_core.B.ToDouble(),
                 center_core.y.ToDouble() / ax_core.B.ToDouble(),
                 center_core.z.ToDouble() / ax_core.B.ToDouble()};
  std::cout << "v_core: len=" << yocto::length(v_core) << "\n";

  // Check 1,000,000 points on sphere:
  int N = 1000000;
  double c_cage = 0.0041195;
  double c_cone = 0.035;

  int gap_count = 0;
  double min_core_in_gap = 1e9;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    double d0 = yocto::dot(a, u[0]);
    double d1 = yocto::dot(a, u[1]);
    double d2 = yocto::dot(a, u[2]);
    double d3 = yocto::dot(a, u[3]);
    double max_comp = std::max(d1, std::max(d2, d3));

    // Gap condition: max_comp < c_cage AND d0 < c_cone
    if (max_comp < c_cage && d0 < c_cone) {
      gap_count++;
      double d_core = yocto::dot(a, v_core);
      min_core_in_gap = std::min(min_core_in_gap, d_core);
    }
  }

  std::cout << "Total sphere points in gap: " << gap_count << " / " << N << "\n";
  std::cout << "min dot(a, v_core) in the gap: " << min_core_in_gap << "\n";

  return 0;
}
