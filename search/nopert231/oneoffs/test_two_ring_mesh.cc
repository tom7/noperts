#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Pt2 { double x, y; };

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

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
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
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  auto check_pt = [&](Pt2 pt, int a) {
    vec3 p = P0 + pt.x * E1 + pt.y * E2;
    vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
    return yocto::dot(p, v) >= c_core * yocto::length(p);
  };

  auto check_tri = [&](Pt2 p1, Pt2 p2, Pt2 p3) {
    for (size_t a = 0; a < valid_axes.size(); a++) {
      if (check_pt(p1, a) && check_pt(p2, a) && check_pt(p3, a)) return (int)a;
    }
    return -1;
  };

  // We want an outer polygon with N vertices that circumscribes D(0, R):
  // R_outer = R / cos(pi / N)
  // And an inner polygon with N vertices at radius R_inner = 20.
  // Center point (0,0)
  for (int N = 12; N <= 64; N += 4) {
    double R_outer = R / std::cos(M_PI / N);
    double R_inner = 18.0;

    std::vector<Pt2> inner_pts(N), outer_pts(N);
    for (int k = 0; k < N; k++) {
      double th = k * 2.0 * M_PI / N;
      inner_pts[k] = {R_inner * std::cos(th), R_inner * std::sin(th)};
      outer_pts[k] = {R_outer * std::cos(th), R_outer * std::sin(th)};
    }

    Pt2 origin = {0, 0};
    bool ok = true;
    int tri_count = 0;

    // Check inner triangles (origin, inner_pts[k], inner_pts[k+1])
    for (int k = 0; k < N; k++) {
      int next = (k + 1) % N;
      if (check_tri(origin, inner_pts[k], inner_pts[next]) < 0) {
        ok = false; break;
      }
      tri_count++;
    }
    if (!ok) continue;

    // Check outer ring quads split into 2 triangles:
    // (inner[k], outer[k], outer[next]) and (inner[k], outer[next], inner[next])
    for (int k = 0; k < N; k++) {
      int next = (k + 1) % N;
      int a1 = check_tri(inner_pts[k], outer_pts[k], outer_pts[next]);
      int a2 = check_tri(inner_pts[k], outer_pts[next], inner_pts[next]);
      if (a1 < 0 || a2 < 0) {
        ok = false; break;
      }
      tri_count += 2;
    }

    if (ok) {
      std::cout << "SUCCESS! N = " << N << " (total triangles = " << tri_count << ")\n";
      return 0;
    }
  }

  // What about 3 rings? (e.g. r=0..18, 18..40, 40..65)?
  for (int N = 16; N <= 64; N += 4) {
    double R_outer = R / std::cos(M_PI / N);
    double R_mid = 38.0;
    double R_inner = 18.0;

    std::vector<Pt2> inner_pts(N), mid_pts(N), outer_pts(N);
    for (int k = 0; k < N; k++) {
      double th = k * 2.0 * M_PI / N;
      inner_pts[k] = {R_inner * std::cos(th), R_inner * std::sin(th)};
      mid_pts[k]   = {R_mid * std::cos(th), R_mid * std::sin(th)};
      outer_pts[k] = {R_outer * std::cos(th), R_outer * std::sin(th)};
    }

    Pt2 origin = {0, 0};
    bool ok = true;
    int tri_count = 0;

    for (int k = 0; k < N; k++) {
      int next = (k + 1) % N;
      if (check_tri(origin, inner_pts[k], inner_pts[next]) < 0) {
        ok = false; break;
      }
      tri_count++;
    }
    if (!ok) continue;

    for (int k = 0; k < N; k++) {
      int next = (k + 1) % N;
      if (check_tri(inner_pts[k], mid_pts[k], mid_pts[next]) < 0 ||
          check_tri(inner_pts[k], mid_pts[next], inner_pts[next]) < 0) {
        ok = false; break;
      }
      tri_count += 2;
    }
    if (!ok) continue;

    for (int k = 0; k < N; k++) {
      int next = (k + 1) % N;
      if (check_tri(mid_pts[k], outer_pts[k], outer_pts[next]) < 0 ||
          check_tri(mid_pts[k], outer_pts[next], mid_pts[next]) < 0) {
        ok = false; break;
      }
      tri_count += 2;
    }

    if (ok) {
      std::cout << "SUCCESS with 3 rings! N = " << N << " (total triangles = " << tri_count << ")\n";
      return 0;
    }
  }

  std::cout << "Need more rings or fine sectors.\n";
  return 0;
}
