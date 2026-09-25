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

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double psi = 60.0125 * M_PI / 180.0;
  double phi = 321.75 * M_PI / 180.0;
  vec3 B = yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));

  std::cout << "Top 10 axes at B:\n";
  std::vector<std::pair<double, int>> dots;
  for (size_t a = 0; a < axes.size(); a++) {
    vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
    dots.push_back({yocto::dot(B, v), (int)a});
  }
  std::sort(dots.rbegin(), dots.rend());
  for (int i = 0; i < 10; i++) {
    std::cout << "  Axis " << dots[i].second << ": dot = " << dots[i].first << "\n";
  }

  // Also check if any annular axis covers B:
  ContactInfo c1[3] = { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(2, 1, 1, 4, 333, 1) };
  ContactInfo c2[3] = { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 666, 15), MakeContact(3, 2, 2, 1, 0, 2) };
  ContactInfo c3[3] = { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(1, 4, 4, 8, 333, 4), MakeContact(15, 19, 19, 3, 1000, 19) };

  AxisCertificate a1, a2, a3;
  BigVecQ3 v1, v2, v3;
  Tube229::AuditAxis(tri, c1, &a1, &v1, &del0, &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c2, &a2, &v2, &del0, &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c3, &a3, &v3, &del0, &err, BigRat(1, 1000));

  vec3 n1 = vec3{v1.x.ToDouble() / a1.B.ToDouble(), v1.y.ToDouble() / a1.B.ToDouble(), v1.z.ToDouble() / a1.B.ToDouble()};
  vec3 n2 = vec3{v2.x.ToDouble() / a2.B.ToDouble(), v2.y.ToDouble() / a2.B.ToDouble(), v2.z.ToDouble() / a2.B.ToDouble()};
  vec3 n3 = vec3{v3.x.ToDouble() / a3.B.ToDouble(), v3.y.ToDouble() / a3.B.ToDouble(), v3.z.ToDouble() / a3.B.ToDouble()};

  std::cout << "Annular axes at B:\n";
  std::cout << "  ax1 dot = " << yocto::dot(B, n1) << "\n";
  std::cout << "  ax2 dot = " << yocto::dot(B, n2) << "\n";
  std::cout << "  ax3 dot = " << yocto::dot(B, n3) << "\n";

  // And ax0 center dot:
  vec3 v0 = vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  std::cout << "  ax0 dot = " << yocto::dot(B, v0) << "\n";

  return 0;
}
