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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Annular axis:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));
  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  std::cout << "Exact annular B: " << ax_ann.B.ToString() << "\n";
  std::cout << "Exact annular delta: " << del_ann.ToString() << "\n";
  std::cout << "Exact annular center: (" << ctr_ann.x.ToString() << ", " << ctr_ann.y.ToString() << ", " << ctr_ann.z.ToString() << ")\n";

  // Core candidate 1 (v=15 at mix=400):
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  bool ok = Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  std::cout << "Audit core: " << (ok ? "SUCCESS" : ("FAIL: " + err)) << "\n";
  if (ok) {
    std::cout << "Exact core B: " << ax_core.B.ToString() << "\n";
    std::cout << "Exact core delta: " << del_core.ToString() << "\n";
    std::cout << "Exact core center: (" << ctr_core.x.ToString() << ", " << ctr_core.y.ToString() << ", " << ctr_core.z.ToString() << ")\n";
  }
  if (ok) {
    vec3 uc = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
               ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
               ctr_core.z.ToDouble() / ax_core.B.ToDouble()};
    vec3 uc_dir = yocto::normalize(uc);
    double dot = yocto::dot(u0_dir, uc_dir);
    double ang = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
    std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), |u0|=" << yocto::length(u0) << "\n";
    std::cout << "uc: (" << uc.x << ", " << uc.y << ", " << uc.z << "), |uc|=" << yocto::length(uc) << "\n";
    std::cout << "dot(u0_dir, uc_dir) = " << dot << ", angle = " << ang << " deg\n";
    std::cout << "B_core = " << ax_core.B.ToDouble() << ", delta_core = " << del_core.ToDouble() << "\n";
  }
  return 0;
}
