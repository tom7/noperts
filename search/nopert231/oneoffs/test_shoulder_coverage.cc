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

  // Shoulder axis with zero defect:
  ContactInfo c_sh[3] = {
    c0[0], c0[1], MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_sh;
  BigVecQ3 center_sh;
  BigRat delta_sh;
  if (!Tube229::AuditAxis(tri, c_sh, &ax_sh, &center_sh, &delta_sh, &err, BigRat(0))) {
    std::cout << "Audit shoulder failed: " << err << "\n";
    return 1;
  }
  vec3 v_sh = {center_sh.x.ToDouble() / ax_sh.B.ToDouble(),
               center_sh.y.ToDouble() / ax_sh.B.ToDouble(),
               center_sh.z.ToDouble() / ax_sh.B.ToDouble()};

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ") norm=" << yocto::length(u0) << "\n";
  std::cout << "v_sh: (" << v_sh.x << ", " << v_sh.y << ", " << v_sh.z << ") norm=" << yocto::length(v_sh) << "\n";

  ContactInfo comp[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  vec3 comp_v[3];
  for (int i = 0; i < 3; i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, comp[i], &ax, &ctr, &del, &err, BigRat(0));
    comp_v[i] = {ctr.x.ToDouble() / ax.B.ToDouble(),
                 ctr.y.ToDouble() / ax.B.ToDouble(),
                 ctr.z.ToDouble() / ax.B.ToDouble()};
  }

  // Check 100,000 points on sphere:
  int N = 100000;
  double min_ann_margin = 1e9;
  int annulus_count = 0;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    double dot_u0 = yocto::dot(a, u0);
    // Annulus condition: 0.002 <= dot_u0 <= 0.040
    if (dot_u0 >= 0.002 && dot_u0 <= 0.040) {
      annulus_count++;
      double max_dot = std::max({
        yocto::dot(a, comp_v[0]),
        yocto::dot(a, comp_v[1]),
        yocto::dot(a, comp_v[2]),
        yocto::dot(a, v_sh)
      });
      if (max_dot < min_ann_margin) {
        min_ann_margin = max_dot;
      }
    }
  }

  std::cout << "Annulus points tested: " << annulus_count << "\n";
  std::cout << "Min combined margin in annulus: " << min_ann_margin << "\n";

  return 0;
}

