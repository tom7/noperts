#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Tri {
  vec3 v0, v1, v2;
  int depth;
};

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

  double c_core = 0.0008;

  std::vector<vec3> ax_v;
  for (size_t i = 0; i < axes.size(); i++) {
    ax_v.push_back(yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                         axes[i].center.y.ToDouble(),
                                         axes[i].center.z.ToDouble()}));
  }

  int N_th = 32;
  int N_ph = 128;
  std::vector<Tri> queue;

  for (int it = 0; it < N_th; it++) {
    double th0 = (double)it / N_th * alpha;
    double th1 = (double)(it + 1) / N_th * alpha;
    for (int ip = 0; ip < N_ph; ip++) {
      double ph0 = 2.0 * M_PI * ip / N_ph;
      double ph1 = 2.0 * M_PI * (ip + 1) / N_ph;

      vec3 p00 = yocto::normalize(std::cos(th0) * u0 + std::sin(th0) * (std::cos(ph0) * e1 + std::sin(ph0) * e2));
      vec3 p01 = yocto::normalize(std::cos(th0) * u0 + std::sin(th0) * (std::cos(ph1) * e1 + std::sin(ph1) * e2));
      vec3 p10 = yocto::normalize(std::cos(th1) * u0 + std::sin(th1) * (std::cos(ph0) * e1 + std::sin(ph0) * e2));
      vec3 p11 = yocto::normalize(std::cos(th1) * u0 + std::sin(th1) * (std::cos(ph1) * e1 + std::sin(ph1) * e2));

      if (it == 0) {
        queue.push_back({u0, p10, p11, 0});
      } else {
        queue.push_back({p00, p10, p11, 0});
        queue.push_back({p00, p11, p01, 0});
      }
    }
  }

  // Let's just find which initial triangle fails at depth 0
  int failing_initial = 0;
  for (auto& t : queue) {
    int covering = -1;
    for (size_t i = 0; i < ax_v.size(); i++) {
      if (yocto::dot(t.v0, ax_v[i]) >= c_core &&
          yocto::dot(t.v1, ax_v[i]) >= c_core &&
          yocto::dot(t.v2, ax_v[i]) >= c_core) {
        covering = i;
        break;
      }
    }
    if (covering == -1) {
      failing_initial++;
      double d0 = -1e9, d1 = -1e9, d2 = -1e9;
      int b0 = -1, b1 = -1, b2 = -1;
      for (size_t i = 0; i < ax_v.size(); i++) {
        if (yocto::dot(t.v0, ax_v[i]) > d0) { d0 = yocto::dot(t.v0, ax_v[i]); b0 = i; }
        if (yocto::dot(t.v1, ax_v[i]) > d1) { d1 = yocto::dot(t.v1, ax_v[i]); b1 = i; }
        if (yocto::dot(t.v2, ax_v[i]) > d2) { d2 = yocto::dot(t.v2, ax_v[i]); b2 = i; }
      }
      std::cout << "Initial tri failed: best v0=" << d0 << " (ax " << b0 << "), v1=" << d1 << " (ax " << b1 << "), v2=" << d2 << " (ax " << b2 << ")\n";
      break;
    }
  }

  return 0;
}
