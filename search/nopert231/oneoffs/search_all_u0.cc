#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static double Det3(vec3 a, vec3 b, vec3 c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> fine_mixes;
  for (int m = 0; m <= 1000; m += 200) fine_mixes.push_back(m);

  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  std::cout << "Silhouette contacts: " << contacts.size() << "\n";

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  std::vector<vec3> p;
  std::string err;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      p.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                   ctr.y.ToDouble() / cert.B.ToDouble(),
                   ctr.z.ToDouble() / cert.B.ToDouble()});
    }
  }
  std::cout << "Zero-defect hull axes: " << p.size() << "\n";

  int valid_u0_count = 0;
  int cagable_u0_count = 0;

  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo c[3] = {contacts[i], contacts[j], contacts[k]};
        AxisCertificate ax; BigVecQ3 ctr; BigRat del;
        if (!Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 100))) continue;
        valid_u0_count++;

        vec3 u0 = {ctr.x.ToDouble() / ax.B.ToDouble(),
                   ctr.y.ToDouble() / ax.B.ToDouble(),
                   ctr.z.ToDouble() / ax.B.ToDouble()};
        vec3 target_ray = -u0;

        // Check if target_ray is in conical hull of any triple of p:
        bool in_cone = false;
        for (size_t a = 0; a < p.size() && !in_cone; a++) {
          for (size_t b = a + 1; b < p.size() && !in_cone; b++) {
            for (size_t c_idx = b + 1; c_idx < p.size(); c_idx++) {
              double d = Det3(p[a], p[b], p[c_idx]);
              if (std::abs(d) < 1e-12) continue;
              double l0 = Det3(target_ray, p[b], p[c_idx]) / d;
              double l1 = Det3(p[a], target_ray, p[c_idx]) / d;
              double l2 = Det3(p[a], p[b], target_ray) / d;
              if (l0 > 0 && l1 > 0 && l2 > 0) {
                in_cone = true;
                break;
              }
            }
          }
        }
        if (in_cone) {
          cagable_u0_count++;
          double min_ang = 180.0;
          vec3 u0_dir = yocto::normalize(u0);
          for (const auto &pk : p) {
            double dot = yocto::dot(u0_dir, yocto::normalize(pk));
            double ang = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
            if (ang < min_ang) min_ang = ang;
          }
          std::cout << "Found cagable u0! ||u0|| = " << yocto::length(u0)
                    << ", delta = " << del.ToDouble()
                    << ", min angle to zero-defect core axis = " << min_ang << " deg\n";
          if (min_ang < 20.0) {
            std::cout << "WINNER! min_ang < 20 deg!\n";
            return 0;
          }
        }
      }
    }
  }
  std::cout << "Done! Valid u0: " << valid_u0_count << ", cagable u0: " << cagable_u0_count << "\n";
  return 0;
}
