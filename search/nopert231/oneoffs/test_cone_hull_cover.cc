#include <iostream>
#include <iomanip>
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
  TriangleQ tri = TriangleFromPath("03121303021");

  // Axis 0 (sib0)
  ContactInfo sib0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string fail0;
  Tube229::AuditAxis(tri, sib0, &cert0, &center0, &delta0, &fail0, BigRat(1, 1000));
  vec3 c0 = yocto::normalize(vec3{center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()});

  // Inner core axis (cert_hull)
  ContactInfo hull[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate cert_h;
  BigVecQ3 center_h;
  BigRat delta_h;
  std::string fail_h;
  bool ok_h = Tube229::AuditAxis(tri, hull, &cert_h, &center_h, &delta_h, &fail_h);
  std::cout << "Hull audit ok=" << ok_h << " fail=" << fail_h << "\n";
  vec3 ch = yocto::normalize(vec3{center_h.x.ToDouble(), center_h.y.ToDouble(), center_h.z.ToDouble()});

  double mu = yocto::dot(c0, ch);
  std::cout << "mu = dot(c0, ch) = " << mu << "\n";

  for (double c_cone : {0.99, 0.995, 0.999, 0.9995, 0.9999}) {
    double s_cone = std::sqrt(1.0 - c_cone * c_cone);
    double s_mu = std::sqrt(1.0 - mu * mu);
    double min_dot = c_cone * mu - s_cone * s_mu;
    std::cout << "c_cone = " << std::setw(6) << c_cone
              << " min_dot = " << std::setw(10) << min_dot
              << (min_dot > 0 ? " > 0 (COVERS!)" : " <= 0") << "\n";
  }

  return 0;
}
