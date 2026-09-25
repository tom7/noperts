#include <iostream>
#include <vector>
#include <cmath>
#include <set>
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
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.z.ToDouble() / ax0.B.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.020;
  double c_core = 0.0005;

  // In plane <x, u0_unnormalized> = 1:
  // p = P0 + X*ex + Y*ey
  // where P0 = u0_unnorm / |u0_unnorm|^2
  vec3 u0_unnorm = vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                        ctr0.y.ToDouble() / ax0.B.ToDouble(),
                        ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 P0 = u0_unnorm / (norm_u0 * norm_u0);
  double R = std::sqrt(1.0 / (c_cone * c_cone) - 1.0 / (norm_u0 * norm_u0));

  std::cout << "norm_u0 = " << norm_u0 << ", R = " << R << "\n";

  auto check_pt = [&](double X, double Y, int a) {
    vec3 p = P0 + X * ex + Y * ey;
    vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
    return yocto::dot(p, v) >= c_core * yocto::length(p);
  };

  auto find_axis = [&](double x1, double x2, double y1, double y2) {
    for (size_t a = 0; a < axes.size(); a++) {
      if (check_pt(x1, y1, a) && check_pt(x2, y1, a) &&
          check_pt(x2, y2, a) && check_pt(x1, y2, a)) {
        return (int)a;
      }
    }
    return -1;
  };

  int leaf_count = 0;
  std::set<int> used_axes;

  auto subdivide = [&](auto& self, double x1, double x2, double y1, double y2, int depth) -> bool {
    int a = find_axis(x1, x2, y1, y2);
    if (a >= 0) {
      leaf_count++;
      used_axes.insert(a);
      return true;
    }
    if (depth >= 10) return false;
    double xm = (x1 + x2) / 2.0;
    double ym = (y1 + y2) / 2.0;
    return self(self, x1, xm, y1, ym, depth + 1) &&
           self(self, xm, x2, y1, ym, depth + 1) &&
           self(self, x1, xm, ym, y2, depth + 1) &&
           self(self, xm, x2, ym, y2, depth + 1);
  };

  bool ok = subdivide(subdivide, -R, R, -R, R, 0);
  std::cout << "Quadtree on [-R, R]^2: ok=" << ok
            << ", leaf_count=" << leaf_count
            << ", used_axes=" << used_axes.size() << "\n";
  std::cout << "Axes: ";
  for (int a : used_axes) std::cout << a << " ";
  std::cout << "\n";

  return 0;
}
