#include <iostream>
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
  std::string target = "03121303022";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo cont0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo cont_hull[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };

  AxisCertificate ax0, ax_h;
  BigVecQ3 c0, ch;
  BigRat d0, dh;
  std::string err;

  Tube229::AuditAxis(tri, cont0, &ax0, &c0, &d0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, cont_hull, &ax_h, &ch, &dh, &err, BigRat(0));

  vec3 u0 = {c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};
  vec3 uh = {ch.x.ToDouble(), ch.y.ToDouble(), ch.z.ToDouble()};

  double c_cone = 0.004714;
  double min_uh = 999.0;

  int N = 2000000;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    if (yocto::dot(a, u0) >= c_cone) {
      double d = yocto::dot(a, uh);
      if (d < min_uh) min_uh = d;
    }
  }

  std::cout << "Inside cone a · u0 >= " << c_cone << ":\n"
            << "  min (a · uh) = " << min_uh << "\n";

  return 0;
}
