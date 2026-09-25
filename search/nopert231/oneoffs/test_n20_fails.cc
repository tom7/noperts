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
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.z.ToDouble() / ax0.B.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0003;

  int N = 20;
  int rings = 2;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  auto get_pt = [&](int r, int k) {
    if (r == 0) return u0;
    double psi = (double)r / rings * psi_outer;
    double phi = k * 2.0 * M_PI / N;
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto check_tri = [&](vec3 p1, vec3 p2, vec3 p3) {
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

  // Check ring 0 (apex triangles):
  for (int k = 0; k < N; k++) {
    int next_k = (k + 1) % N;
    int ax = check_tri(u0, get_pt(1, k), get_pt(1, next_k));
    if (ax < 0) std::cout << "Apex tri " << k << " FAILED\n";
  }

  // Check quads:
  for (int k = 0; k < N; k++) {
    int next_k = (k + 1) % N;
    vec3 A = get_pt(1, k);
    vec3 B = get_pt(2, k);
    vec3 C = get_pt(2, next_k);
    vec3 D = get_pt(1, next_k);

    int t1 = check_tri(A, B, C);
    int t2 = check_tri(A, C, D);
    int t3 = check_tri(B, C, D);
    int t4 = check_tri(B, D, A);

    if ((t1 >= 0 && t2 >= 0) || (t3 >= 0 && t4 >= 0)) {
      // passed
    } else {
      std::cout << "Quad k=" << k << " FAILED! Angles: phi in ["
                << k * 360.0 / N << ", " << (k + 1) * 360.0 / N << "]\n";
      std::cout << "  t1=" << t1 << " t2=" << t2 << " t3=" << t3 << " t4=" << t4 << "\n";
    }
  }

  return 0;
}
