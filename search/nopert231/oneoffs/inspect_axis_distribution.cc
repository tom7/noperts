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

  std::cout << "Audited axes: " << axes.size() << "\n";
  int pos_lambda = 0, neg_lambda = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    double lambda = yocto::dot(v, u0);
    double phi = std::atan2(yocto::dot(v, e2), yocto::dot(v, e1)) * 180.0 / M_PI;
    double theta = std::acos(std::clamp(lambda, -1.0, 1.0)) * 180.0 / M_PI;
    if (lambda > 0) pos_lambda++; else neg_lambda++;
  }
  std::cout << "pos_lambda: " << pos_lambda << ", neg_lambda: " << neg_lambda << "\n";

  // Histogram of phi for axes with lambda > 0
  int phi_bins[12] = {0};
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    double lambda = yocto::dot(v, u0);
    if (lambda <= 0) continue;
    double phi = std::atan2(yocto::dot(v, e2), yocto::dot(v, e1)) * 180.0 / M_PI;
    if (phi < 0) phi += 360.0;
    int bin = std::clamp((int)(phi / 30.0), 0, 11);
    phi_bins[bin]++;
  }
  std::cout << "Azimuthal phi distribution (30 deg bins) for axes with lambda > 0:\n";
  for (int b = 0; b < 12; b++) {
    std::cout << "  [" << b*30 << " .. " << (b+1)*30 << " deg]: " << phi_bins[b] << " axes\n";
  }

  return 0;
}
