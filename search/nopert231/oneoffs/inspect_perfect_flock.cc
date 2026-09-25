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

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0005;

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

  for (auto [num_rings, N] : std::vector<std::pair<int, int>>{{4, 24}, {3, 36}}) {
    double tan_outer = std::tan(alpha) / std::cos(M_PI / N);
    double psi_outer = std::atan(tan_outer);
    double psi_step = psi_outer / num_rings;

    std::vector<CertTriangle> all_triangles;
    for (int k = 0; k < N; k++) {
      double phi1 = k * 2.0 * M_PI / N;
      double phi2 = (k + 1) * 2.0 * M_PI / N;
      vec3 A = u0;
      vec3 B = get_pt(psi_step, phi1);
      vec3 C = get_pt(psi_step, phi2);
      int a = check_tri(A, B, C);
      all_triangles.push_back({A, B, C, a});
    }

    for (int ring = 1; ring < num_rings; ring++) {
      double r1 = ring * psi_step;
      double r2 = (ring + 1) * psi_step;
      for (int k = 0; k < N; k++) {
        double phi1 = k * 2.0 * M_PI / N;
        double phi2 = (k + 1) * 2.0 * M_PI / N;
        vec3 A = get_pt(r1, phi1);
        vec3 B = get_pt(r2, phi1);
        vec3 C = get_pt(r2, phi2);
        vec3 D = get_pt(r1, phi2);
        int t1 = check_tri(A, B, C);
        int t2 = check_tri(A, C, D);
        if (t1 >= 0 && t2 >= 0) {
          all_triangles.push_back({A, B, C, t1});
          all_triangles.push_back({A, C, D, t2});
        } else {
          int t3 = check_tri(B, C, D);
          int t4 = check_tri(B, D, A);
          all_triangles.push_back({B, C, D, t3});
          all_triangles.push_back({B, D, A, t4});
        }
      }
    }

    std::set<int> unique_axes;
    for (const auto& t : all_triangles) unique_axes.insert(t.axis_idx);
    std::cout << "num_rings=" << num_rings << ", N=" << N << ": "
              << all_triangles.size() << " triangles, "
              << unique_axes.size() << " unique axes. Axes: ";
    for (int a : unique_axes) std::cout << a << " ";
    std::cout << "\n";
  }

  return 0;
}
