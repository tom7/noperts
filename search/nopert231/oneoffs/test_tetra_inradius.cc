#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  std::vector<int> comp_idx = {7, 23, 26};
  std::vector<vec3> u_comp;
  for (int idx : comp_idx) {
    ContactInfo triple[3] = {axes500[idx].cert.contacts[0], axes500[idx].cert.contacts[1], axes500[idx].cert.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &fail, BigRat(0));
    u_comp.push_back({center.x.ToDouble() / cert.B.ToDouble(),
                      center.y.ToDouble() / cert.B.ToDouble(),
                      center.z.ToDouble() / cert.B.ToDouble()});
  }

  // Suppose we rescale:
  // u0 is scaled by s0 = 1 / c_cone
  // u_comp[k] is scaled by s_k = 1 / c_comp
  double c_cone = 0.035;
  for (double c_comp : {0.003, 0.005, 0.010, 0.020, 0.050, 0.100, 0.187}) {
    vec3 v0 = u0 / c_cone;
    vec3 v1 = u_comp[0] / c_comp;
    vec3 v2 = u_comp[1] / c_comp;
    vec3 v3 = u_comp[2] / c_comp;

    // Check minimum over unit sphere:
    int N = 200000;
    double min_cover = 1e9;
    for (int i = 0; i < N; i++) {
      double z = 1.0 - (2.0 * i + 1.0) / N;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi = i * 2.399963229728653;
      vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
      double d = std::max(std::max(yocto::dot(a, v0), yocto::dot(a, v1)),
                          std::max(yocto::dot(a, v2), yocto::dot(a, v3)));
      if (d < min_cover) min_cover = d;
    }
    std::cout << "c_comp = " << c_comp << ": min_cover = " << min_cover << "\n";
  }

  return 0;
}
