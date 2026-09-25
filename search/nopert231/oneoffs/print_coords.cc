#include <iostream>
#include <iomanip>
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int idx1 = 1283, idx2 = 4074, idx3 = 1041;
  vec3 u1 = {base_axes[idx1].center.x.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.y.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.z.ToDouble() / base_axes[idx1].cert.B.ToDouble()};
  vec3 u2 = {base_axes[idx2].center.x.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.y.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.z.ToDouble() / base_axes[idx2].cert.B.ToDouble()};
  vec3 u3 = {base_axes[idx3].center.x.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.y.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.z.ToDouble() / base_axes[idx3].cert.B.ToDouble()};

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "u0: " << u0.x << ", " << u0.y << ", " << u0.z << " (len=" << yocto::length(u0) << ")\n";
  std::cout << "u1: " << u1.x << ", " << u1.y << ", " << u1.z << " (len=" << yocto::length(u1) << ")\n";
  std::cout << "u2: " << u2.x << ", " << u2.y << ", " << u2.z << " (len=" << yocto::length(u2) << ")\n";
  std::cout << "u3: " << u3.x << ", " << u3.y << ", " << u3.z << " (len=" << yocto::length(u3) << ")\n";

  std::cout << "dot(u0, u1): " << yocto::dot(u0, u1) << "\n";
  std::cout << "dot(u0, u2): " << yocto::dot(u0, u2) << "\n";
  std::cout << "dot(u0, u3): " << yocto::dot(u0, u3) << "\n";

  // Let's compute the normal to the triangle u1, u2, u3:
  vec3 n123 = yocto::cross(u2 - u1, u3 - u1);
  std::cout << "n123: " << n123.x << ", " << n123.y << ", " << n123.z << "\n";
  std::cout << "dot(u0, n123): " << yocto::dot(u0, n123) << "\n";
  std::cout << "dot(u1, n123): " << yocto::dot(u1, n123) << "\n";

  return 0;
}
