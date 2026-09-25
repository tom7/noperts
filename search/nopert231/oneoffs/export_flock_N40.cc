#include <iostream>
#include <vector>
#include <set>
#include <map>
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

struct CertTriangle {
  vec3 p1, p2, p3;
  int axis_idx;
  int m_idx;
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

  int N = 40;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  auto get_pt = [&](double psi, double phi) {
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto find_axis = [&](vec3 p1, vec3 p2, vec3 p3) {
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

  std::vector<CertTriangle> all_triangles;

  // 1. Apex triangles
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    vec3 A = u0;
    vec3 B = get_pt(0.5 * psi_outer, phi1);
    vec3 C = get_pt(0.5 * psi_outer, phi2);
    int ax = find_axis(A, B, C);
    if (ax < 0) { std::cerr << "Apex fail at " << k << "\n"; return 1; }
    all_triangles.push_back({A, B, C, ax, -1});
  }

  // 2. Outer quads
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    vec3 A = get_pt(0.5 * psi_outer, phi1);
    vec3 B = get_pt(psi_outer, phi1);
    vec3 C = get_pt(psi_outer, phi2);
    vec3 D = get_pt(0.5 * psi_outer, phi2);

    int t1 = find_axis(A, B, C);
    int t2 = find_axis(A, C, D);
    if (t1 >= 0 && t2 >= 0) {
      all_triangles.push_back({A, B, C, t1, -1});
      all_triangles.push_back({A, C, D, t2, -1});
    } else {
      int t3 = find_axis(B, C, D);
      int t4 = find_axis(B, D, A);
      if (t3 >= 0 && t4 >= 0) {
        all_triangles.push_back({B, C, D, t3, -1});
        all_triangles.push_back({B, D, A, t4, -1});
      } else {
        std::cerr << "Quad fail at " << k << "\n";
        return 1;
      }
    }
  }

  std::set<int> unique_axes;
  for (const auto& t : all_triangles) unique_axes.insert(t.axis_idx);
  std::vector<int> core_axes_list(unique_axes.begin(), unique_axes.end());
  std::map<int, int> axis_to_m;
  for (size_t i = 0; i < core_axes_list.size(); i++) {
    axis_to_m[core_axes_list[i]] = (int)i;
  }
  for (auto& t : all_triangles) {
    t.m_idx = axis_to_m[t.axis_idx];
  }

  std::cout << "SUCCESS! Total triangles: " << all_triangles.size() << "\n";
  std::cout << "Distinct core axes (M): " << unique_axes.size() << "\n";
  std::cout << "Unique axes indices: ";
  for (int a : unique_axes) std::cout << a << " ";
  std::cout << "\n";

  return 0;
}
