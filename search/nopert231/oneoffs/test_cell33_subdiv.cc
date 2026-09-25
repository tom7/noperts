#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.z.ToDouble() / ax0.B.ToDouble()});
  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_core = 0.0003;
  auto get_pt = [&](double psi, double phi) {
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
    for (size_t a = 0; a < axes.size(); a++) {
      vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
      if (yocto::dot(p1, v) >= c_core && yocto::dot(p2, v) >= c_core && yocto::dot(p3, v) >= c_core) {
        return (int)a;
      }
    }
    return -1;
  };

  // Cell (3, 3):
  double p_lo = 54.7693 * M_PI / 180.0;
  double p_hi = 58.4206 * M_PI / 180.0;
  double f_lo = 321.75 * M_PI / 180.0;
  double f_hi = 324.0 * M_PI / 180.0;

  for (int grid : {2, 3, 4, 5, 6, 8, 10}) {
    int fail = 0;
    for (int i = 0; i < grid; i++) {
      for (int j = 0; j < grid; j++) {
        double pa = p_lo + (p_hi - p_lo) * i / grid;
        double pb = p_lo + (p_hi - p_lo) * (i + 1) / grid;
        double fa = f_lo + (f_hi - f_lo) * j / grid;
        double fb = f_lo + (f_hi - f_lo) * (j + 1) / grid;
        vec3 A = get_pt(pa, fa);
        vec3 B = get_pt(pb, fa);
        vec3 C = get_pt(pb, fb);
        vec3 D = get_pt(pa, fb);

        bool d1 = (check_tri(A, B, C) >= 0 && check_tri(A, C, D) >= 0);
        bool d2 = (check_tri(B, C, D) >= 0 && check_tri(B, D, A) >= 0);
        if (!d1 && !d2) fail++;
      }
    }
    std::cout << "Cell (3, 3) grid " << grid << "x" << grid << ": fail = " << fail << "\n";
    if (fail == 0) break;
  }

  // Also check Cell (3, 1) and (3, 2):
  for (int cell_j : {1, 2}) {
    double f1 = (315.0 + cell_j * 2.25) * M_PI / 180.0;
    double f2 = (315.0 + (cell_j + 1) * 2.25) * M_PI / 180.0;
    for (int grid : {2, 3, 4, 5}) {
      int fail = 0;
      for (int i = 0; i < grid; i++) {
        for (int j = 0; j < grid; j++) {
          double pa = p_lo + (p_hi - p_lo) * i / grid;
          double pb = p_lo + (p_hi - p_lo) * (i + 1) / grid;
          double fa = f1 + (f2 - f1) * j / grid;
          double fb = f1 + (f2 - f1) * (j + 1) / grid;
          vec3 A = get_pt(pa, fa);
          vec3 B = get_pt(pb, fa);
          vec3 C = get_pt(pb, fb);
          vec3 D = get_pt(pa, fb);
          bool d1 = (check_tri(A, B, C) >= 0 && check_tri(A, C, D) >= 0);
          bool d2 = (check_tri(B, C, D) >= 0 && check_tri(B, D, A) >= 0);
          if (!d1 && !d2) fail++;
        }
      }
      std::cout << "Cell (3, " << cell_j << ") grid " << grid << "x" << grid << ": fail = " << fail << "\n";
      if (fail == 0) break;
    }
  }

  return 0;
}
