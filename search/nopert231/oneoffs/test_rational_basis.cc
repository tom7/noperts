#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>
#include <set>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);

  vec3 E1 = vec3{1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = vec3{0.0, 1.0, -u0.y / u0.z};

  vec3 P0 = u0 / norm_u0_sq;
  double c_cone = 0.035;
  double c_core = 0.000234060;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);
  std::cout << "R = " << R << "\n";

  // Filter axes by delta <= box_delta
  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) {
      valid_axes.push_back(ax);
    }
  }

  // Fine grid of mixes for contact triple (1, 15, 2)
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({cert, ctr, del});
        }
      }
    }
  }

  // Also finer sweep around m1=1000, m2=300
  for (int m1 : {700, 800, 850, 900, 950, 1000}) {
    for (int m2 = 200; m2 <= 400; m2 += 10) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({cert, ctr, del});
        }
      }
    }
  }

  std::cout << "Valid axes with delta <= box_delta: " << valid_axes.size() << "\n";

  auto check_pt = [&](double X, double Y, int a) {
    vec3 p = P0 + X * E1 + Y * E2;
    vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
    return yocto::dot(p, v) >= c_core * yocto::length(p);
  };

  auto find_tri_axis = [&](double xa, double ya, double xb, double yb, double xc, double yc) {
    for (size_t a = 0; a < valid_axes.size(); a++) {
      if (check_pt(xa, ya, a) && check_pt(xb, yb, a) && check_pt(xc, yc, a)) {
        return (int)a;
      }
    }
    return -1;
  };

  auto dist_sq_to_segment = [&](double px, double py, double qx, double qy) {
    vec3 V0 = px * E1 + py * E2;
    vec3 dV = (qx - px) * E1 + (qy - py) * E2;
    double dV_sq = yocto::dot(dV, dV);
    if (dV_sq < 1e-15) return yocto::dot(V0, V0);
    double t = -yocto::dot(V0, dV) / dV_sq;
    t = std::max(0.0, std::min(1.0, t));
    vec3 Vt = V0 + t * dV;
    return yocto::dot(Vt, Vt);
  };

  // Check if triangle is completely outside disk of radius R
  auto tri_outside_disk = [&](double x1, double y1, double x2, double y2, double x3, double y3) {
    // Check if origin is inside 2D triangle:
    // Using cross products of 2D edges:
    auto cross2 = [](double ax, double ay, double bx, double by) {
      return ax * by - ay * bx;
    };
    double c1 = cross2(x2 - x1, y2 - y1, -x1, -y1);
    double c2 = cross2(x3 - x2, y3 - y2, -x2, -y2);
    double c3 = cross2(x1 - x3, y1 - y3, -x3, -y3);
    if ((c1 >= 0 && c2 >= 0 && c3 >= 0) || (c1 <= 0 && c2 <= 0 && c3 <= 0)) {
      // Origin is inside triangle, so min distance to origin is 0 <= R
      return false;
    }
    // Min distance to the 3 edges:
    double min_d_sq = std::min({
      dist_sq_to_segment(x1, y1, x2, y2),
      dist_sq_to_segment(x2, y2, x3, y3),
      dist_sq_to_segment(x3, y3, x1, y1)
    });
    return min_d_sq > R_sq;
  };

  int tri_leaf_count = 0;
  std::set<int> tri_used_axes;

  auto subdivide_tri = [&](auto& self,
                           double x1, double y1,
                           double x2, double y2,
                           double x3, double y3, int depth) -> bool {
    // If triangle is completely outside disk, it needs no core coverage!
    if (tri_outside_disk(x1, y1, x2, y2, x3, y3)) {
      return true;
    }

    int a = find_tri_axis(x1, y1, x2, y2, x3, y3);
    if (a >= 0) {
      tri_leaf_count++;
      tri_used_axes.insert(a);
      return true;
    }
    if (depth >= 20) {
      std::cout << "Depth 20 reached at (" << x1 << "," << y1 << ") (" << x2 << "," << y2 << ") (" << x3 << "," << y3 << ")\n";
      return false;
    }

    // Midpoints
    double m12x = 0.5 * (x1 + x2), m12y = 0.5 * (y1 + y2);
    double m23x = 0.5 * (x2 + x3), m23y = 0.5 * (y2 + y3);
    double m31x = 0.5 * (x3 + x1), m31y = 0.5 * (y3 + y1);

    return self(self, x1, y1, m12x, m12y, m31x, m31y, depth + 1) &&
           self(self, m12x, m12y, x2, y2, m23x, m23y, depth + 1) &&
           self(self, m31x, m31y, m23x, m23y, x3, y3, depth + 1) &&
           self(self, m12x, m12y, m23x, m23y, m31x, m31y, depth + 1);
  };

  double L = 22.0;
  // Two triangles covering [-L, L]^2
  bool ok1 = subdivide_tri(subdivide_tri, -L, -L,  L, -L,  L,  L, 0);
  bool ok2 = subdivide_tri(subdivide_tri, -L, -L,  L,  L, -L,  L, 0);

  std::cout << "Triangle coverage: ok1=" << ok1 << ", ok2=" << ok2
            << ", total leaves=" << tri_leaf_count
            << ", used axes=" << tri_used_axes.size() << "\n";
  std::cout << "Axes: ";
  for (int a : tri_used_axes) std::cout << a << " ";
  std::cout << "\n";

  return 0;
}
