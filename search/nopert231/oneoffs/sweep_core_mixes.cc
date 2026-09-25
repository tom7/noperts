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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(1, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 dir0 = yocto::normalize(u0);

  std::cout << "Sweeping mixes around coreAxis (800, 800, 400)...\n";
  double min_angle = 180.0;
  int best_m0 = -1, best_m1 = -1, best_m2 = -1;

  for (int m0 = 0; m0 <= 1000; m0 += 50) {
    for (int m1 = 0; m1 <= 1000; m1 += 50) {
      for (int m2 = 0; m2 <= 1000; m2 += 50) {
        ContactInfo core[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(14, 15, 15, 19, m2, 15)
        };
        AxisCertificate cert;
        BigVecQ3 center;
        BigRat delta;
        if (Tube229::AuditAxis(tri, core, &cert, &center, &delta, &err, BigRat(0))) {
          vec3 uc = {center.x.ToDouble() / cert.B.ToDouble(),
                     center.y.ToDouble() / cert.B.ToDouble(),
                     center.z.ToDouble() / cert.B.ToDouble()};
          double dot = yocto::dot(dir0, yocto::normalize(uc));
          double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
          if (angle < min_angle) {
            min_angle = angle;
            best_m0 = m0; best_m1 = m1; best_m2 = m2;
            std::cout << "New closest zero-defect axis: angle = " << angle
                      << " deg with mixes (" << m0 << ", " << m1 << ", " << m2 << ")\n";
          }
        }
      }
    }
  }

  std::cout << "Done sweep. Best angle: " << min_angle << " deg\n";
  return 0;
}
