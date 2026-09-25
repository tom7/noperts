#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  int N_sectors = 32;
  int N_rings = 8;
  int r = 5;
  int s = 28;
  double theta0 = (double)r / N_rings * alpha;
  double theta1 = (double)(r + 1) / N_rings * alpha;
  double phi0 = 2.0 * M_PI * s / N_sectors;
  double phi1 = 2.0 * M_PI * (s + 1) / N_sectors;

  auto pt = [&](double th, double ph) -> vec3 {
    return std::cos(th) * u0 + std::sin(th) * (std::cos(ph) * e1 + std::sin(ph) * e2);
  };
  vec3 p00 = pt(theta0, phi0);
  vec3 p01 = pt(theta0, phi1);
  vec3 p10 = pt(theta1, phi0);
  vec3 p11 = pt(theta1, phi1);

  vec3 v3058 = yocto::normalize(vec3{axes[3058].center.x.ToDouble(), axes[3058].center.y.ToDouble(), axes[3058].center.z.ToDouble()});

  std::cout << "Axis 3058 dots:\n";
  std::cout << "  p00: " << yocto::dot(p00, v3058) << "\n";
  std::cout << "  p01: " << yocto::dot(p01, v3058) << "\n";
  std::cout << "  p10: " << yocto::dot(p10, v3058) << "\n";
  std::cout << "  p11: " << yocto::dot(p11, v3058) << "\n";

  return 0;
}
