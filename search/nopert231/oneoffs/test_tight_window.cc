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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Annular axis u0:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  // Core axis:
  ContactInfo c_core[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax_core; BigVecQ3 ctr_core; BigRat del_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  vec3 v0 = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
             ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
             ctr_core.z.ToDouble() / ax_core.B.ToDouble()};

  double norm_u0 = yocto::length(u0);
  double norm_v0 = yocto::length(v0);
  vec3 u0_dir = yocto::normalize(u0);
  vec3 v0_dir = yocto::normalize(v0);

  double dot_uv = yocto::dot(u0_dir, v0_dir);
  double theta = std::acos(dot_uv) * 180.0 / M_PI;

  std::cout << "||u0|| = " << norm_u0 << ", ||v0|| = " << norm_v0 << ", theta = " << theta << " deg\n";
  std::cout << "Max allowed c_cone for barycentric (4/7 * ||u0||): " << (4.0 / 7.0) * norm_u0 << "\n";
  std::cout << "Min required c_cone for single axis (sin(theta) * ||u0||): " << std::sin(theta * M_PI / 180.0) * norm_u0 << "\n";

  for (double c_cone = 0.0276; c_cone <= 0.0292; c_cone += 0.0002) {
    double cos_alpha = c_cone / norm_u0;
    double alpha = std::acos(cos_alpha);
    double worst_angle = alpha + theta * M_PI / 180.0;
    double worst_inner = norm_v0 * std::cos(worst_angle);
    std::cout << "c_cone = " << c_cone << ": alpha = " << alpha * 180.0 / M_PI
              << " deg, worst_angle = " << worst_angle * 180.0 / M_PI
              << " deg, worst_inner = " << worst_inner << "\n";
  }

  return 0;
}
