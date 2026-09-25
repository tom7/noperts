#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iomanip>
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

std::vector<vec3> GenerateCapPoints(const vec3 &u0, double alpha_rad, int num_points) {
  std::vector<vec3> pts;
  vec3 z = u0;
  vec3 x = yocto::normalize(yocto::cross(z, std::abs(z.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 y = yocto::cross(z, x);

  double cos_max = std::cos(alpha_rad);
  for (int i = 0; i < num_points; i++) {
    double t = (double)i / (double)(num_points - 1);
    double cos_theta = 1.0 - t * (1.0 - cos_max);
    double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
    double phi = i * 2.399963229728653;
    vec3 p = (std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z;
    pts.push_back(yocto::normalize(p));
  }
  return pts;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                     ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  std::cout << "u0 norm: " << norm_u0 << ", c_cone: " << c_cone << ", alpha: " << alpha * 180.0 / M_PI << " deg\n";
  auto cap_pts = GenerateCapPoints(u0, alpha, 4000);

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  // Greedy set cover targeting margin >= 0.001
  double target_margin = 0.005;
  std::vector<size_t> chosen_axes;
  std::vector<bool> point_covered(cap_pts.size(), false);
  int covered_count = 0;

  while (covered_count < (int)cap_pts.size()) {
    int best_axis = -1;
    int best_new_covered = -1;

    for (size_t i = 0; i < all_v.size(); i++) {
      int new_cov = 0;
      for (size_t p = 0; p < cap_pts.size(); p++) {
        if (!point_covered[p] && yocto::dot(cap_pts[p], all_v[i]) >= target_margin) {
          new_cov++;
        }
      }
      if (new_cov > best_new_covered) {
        best_new_covered = new_cov;
        best_axis = i;
      }
    }

    if (best_new_covered <= 0) break;

    chosen_axes.push_back(best_axis);
    for (size_t p = 0; p < cap_pts.size(); p++) {
      if (!point_covered[p] && yocto::dot(cap_pts[p], all_v[best_axis]) >= target_margin) {
        point_covered[p] = true;
        covered_count++;
      }
    }
    std::cout << "Added axis " << best_axis << " (contacts: "
              << axes[best_axis].cert.contacts[0].vertex << ", "
              << axes[best_axis].cert.contacts[1].vertex << ", "
              << axes[best_axis].cert.contacts[2].vertex << "), new covered: "
              << best_new_covered << ", total covered: " << covered_count << " / " << cap_pts.size() << "\n";
  }

  std::cout << "\nMinimal flock size found: " << chosen_axes.size() << " axes!\n";
  for (size_t m = 0; m < chosen_axes.size(); m++) {
    const auto &ax = axes[chosen_axes[m]].cert;
    std::cout << "def coreAx" << m << " : AxisCertificate := {\n";
    std::cout << "  edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "],\n";
    std::cout << "  edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "],\n";
    std::cout << "  edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "],\n";
    std::cout << "  edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "],\n";
    std::cout << "  mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "],\n";
    std::cout << "  index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "],\n";
    std::cout << "  nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "],\n";
    std::cout << "  B := " << ax.B.ToString() << "\n";
    std::cout << "}\n\n";
  }
  return 0;
}
