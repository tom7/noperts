#include <iostream>
#include <vector>
#include <set>
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

struct TriInfo {
  vec3 p1, p2, p3;
  int axis_idx;
};

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

  double c_cone = 0.027;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0003;

  int N = 20;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  auto get_pt = [&](double psi, double phi) {
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto find_axis = [&](vec3 p1, vec3 p2, vec3 p3) {
    for (size_t i = 0; i < axes.size(); i++) {
      vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
      if (yocto::dot(p1, v) >= c_core && yocto::dot(p2, v) >= c_core && yocto::dot(p3, v) >= c_core) {
        return (int)i;
      }
    }
    return -1;
  };

  std::vector<TriInfo> triangles;
  std::set<int> distinct_axes;

  // 1. Apex triangles
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    vec3 A = u0;
    vec3 B = get_pt(0.5 * psi_outer, phi1);
    vec3 C = get_pt(0.5 * psi_outer, phi2);
    int ax = find_axis(A, B, C);
    if (ax < 0) { std::cerr << "Apex " << k << " failed!\n"; return 1; }
    triangles.push_back({A, B, C, ax});
    distinct_axes.insert(ax);
  }

  // 2. Outer quads
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    if (k != 17) {
      vec3 A = get_pt(0.5 * psi_outer, phi1);
      vec3 B = get_pt(psi_outer, phi1);
      vec3 C = get_pt(psi_outer, phi2);
      vec3 D = get_pt(0.5 * psi_outer, phi2);
      int t1 = find_axis(A, B, C);
      int t2 = find_axis(A, C, D);
      if (t1 >= 0 && t2 >= 0) {
        triangles.push_back({A, B, C, t1});
        triangles.push_back({A, C, D, t2});
        distinct_axes.insert(t1);
        distinct_axes.insert(t2);
      } else {
        int t3 = find_axis(B, C, D);
        int t4 = find_axis(B, D, A);
        if (t3 >= 0 && t4 >= 0) {
          triangles.push_back({B, C, D, t3});
          triangles.push_back({B, D, A, t4});
          distinct_axes.insert(t3);
          distinct_axes.insert(t4);
        } else {
          std::cerr << "Quad " << k << " failed!\n";
          return 1;
        }
      }
    } else {
      // Split Quad 17 into 2
      for (int step = 0; step < 2; step++) {
        double f1 = phi1 + (phi2 - phi1) * (double)step / 2.0;
        double f2 = phi1 + (phi2 - phi1) * (double)(step + 1) / 2.0;
        vec3 A = get_pt(0.5 * psi_outer, f1);
        vec3 B = get_pt(psi_outer, f1);
        vec3 C = get_pt(psi_outer, f2);
        vec3 D = get_pt(0.5 * psi_outer, f2);
        int t1 = find_axis(A, B, C);
        int t2 = find_axis(A, C, D);
        if (t1 >= 0 && t2 >= 0) {
          triangles.push_back({A, B, C, t1});
          triangles.push_back({A, C, D, t2});
          distinct_axes.insert(t1);
          distinct_axes.insert(t2);
        } else {
          int t3 = find_axis(B, C, D);
          int t4 = find_axis(B, D, A);
          if (t3 >= 0 && t4 >= 0) {
            triangles.push_back({B, C, D, t3});
            triangles.push_back({B, D, A, t4});
            distinct_axes.insert(t3);
            distinct_axes.insert(t4);
          } else {
            std::cerr << "Quad 17 step " << step << " failed!\n";
            return 1;
          }
        }
      }
    }
  }

  std::cout << "SUCCESS! Total triangles: " << triangles.size() << "\n";
  std::cout << "Distinct core axes used: " << distinct_axes.size() << "\n";
  std::cout << "Distinct axes list: ";
  for (int a : distinct_axes) std::cout << a << " ";
  std::cout << "\n";

  return 0;
}
