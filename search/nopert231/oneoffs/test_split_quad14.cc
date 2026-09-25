#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);
  double norm_u0 = yocto::length(u0_raw);

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0001;

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  int N = 16;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);
  double psi_inner = 0.5 * psi_outer;

  // Let's test splitting Quad 14:
  // Quad 14 has phi1 = 14 * 2pi/16, phi2 = 15 * 2pi/16.
  // Let phi_mid = 0.5 * (phi1 + phi2) = 14.5 * 2pi/16.
  // Sub-quad A: [14, 14.5], Sub-quad B: [14.5, 15].
  double phi1 = 14.0 * 2.0 * M_PI / N;
  double phi_mid = 14.5 * 2.0 * M_PI / N;
  double phi2 = 15.0 * 2.0 * M_PI / N;

  vec3 in1 = yocto::normalize(std::cos(psi_inner) * u0 + std::sin(psi_inner) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
  vec3 in_mid = yocto::normalize(std::cos(psi_inner) * u0 + std::sin(psi_inner) * (std::cos(phi_mid) * ex + std::sin(phi_mid) * ey));
  vec3 in2 = yocto::normalize(std::cos(psi_inner) * u0 + std::sin(psi_inner) * (std::cos(phi2) * ex + std::sin(phi2) * ey));

  vec3 out1 = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi1) * ex + std::sin(phi1) * ey));
  vec3 out_mid = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi_mid) * ex + std::sin(phi_mid) * ey));
  vec3 out2 = yocto::normalize(std::cos(psi_outer) * u0 + std::sin(psi_outer) * (std::cos(phi2) * ex + std::sin(phi2) * ey));

  // Check Sub-quad A (in1, out1, out_mid, in_mid)
  bool subA_t1 = false, subA_t2 = false;
  int axA1 = -1, axA2 = -1;
  for (size_t i = 0; i < all_v.size(); i++) {
    if (!subA_t1 && yocto::dot(in1, all_v[i]) >= c_core &&
        yocto::dot(out1, all_v[i]) >= c_core &&
        yocto::dot(out_mid, all_v[i]) >= c_core) { subA_t1 = true; axA1 = i; }
    if (!subA_t2 && yocto::dot(in1, all_v[i]) >= c_core &&
        yocto::dot(out_mid, all_v[i]) >= c_core &&
        yocto::dot(in_mid, all_v[i]) >= c_core) { subA_t2 = true; axA2 = i; }
  }
  std::cout << "Sub-quad A: t1=" << subA_t1 << " (ax " << axA1 << "), t2=" << subA_t2 << " (ax " << axA2 << ")\n";

  // Check Sub-quad B (in_mid, out_mid, out2, in2)
  bool subB_t1 = false, subB_t2 = false;
  int axB1 = -1, axB2 = -1;
  for (size_t i = 0; i < all_v.size(); i++) {
    if (!subB_t1 && yocto::dot(in_mid, all_v[i]) >= c_core &&
        yocto::dot(out_mid, all_v[i]) >= c_core &&
        yocto::dot(out2, all_v[i]) >= c_core) { subB_t1 = true; axB1 = i; }
    if (!subB_t2 && yocto::dot(in_mid, all_v[i]) >= c_core &&
        yocto::dot(out2, all_v[i]) >= c_core &&
        yocto::dot(in2, all_v[i]) >= c_core) { subB_t2 = true; axB2 = i; }
  }
  std::cout << "Sub-quad B: t1=" << subB_t1 << " (ax " << axB1 << "), t2=" << subB_t2 << " (ax " << axB2 << ")\n";

  if (subA_t1 && subA_t2 && subB_t1 && subB_t2) {
    std::cout << "SUCCESS! Subdividing Quad 14 solves the entire cone!\n";
  } else {
    // Check other diagonal on subquads
    bool subA_t1_alt = false, subA_t2_alt = false;
    for (size_t i = 0; i < all_v.size(); i++) {
      if (!subA_t1_alt && yocto::dot(in1, all_v[i]) >= c_core &&
          yocto::dot(out1, all_v[i]) >= c_core &&
          yocto::dot(in_mid, all_v[i]) >= c_core) subA_t1_alt = true;
      if (!subA_t2_alt && yocto::dot(out1, all_v[i]) >= c_core &&
          yocto::dot(out_mid, all_v[i]) >= c_core &&
          yocto::dot(in_mid, all_v[i]) >= c_core) subA_t2_alt = true;
    }
    std::cout << "Sub-quad A (alt diagonal): t1=" << subA_t1_alt << ", t2=" << subA_t2_alt << "\n";
  }

  return 0;
}
