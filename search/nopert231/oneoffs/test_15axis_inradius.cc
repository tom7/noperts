#include <iostream>
#include <vector>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    cand_contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  int C = cand_contacts.size();
  std::vector<vec3> zero_defect_dirs;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          zero_defect_dirs.push_back({center.x.ToDouble() / ax.B.ToDouble(),
                                     center.y.ToDouble() / ax.B.ToDouble(),
                                     center.z.ToDouble() / ax.B.ToDouble()});
        }
      }
    }
  }

  double c_cone = 0.035;
  int N = 50000;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    if (yocto::dot(a, u0) < c_cone) pts.push_back(a);
  }

  std::vector<int> selected_idx;
  std::vector<double> current_max(pts.size(), -1e9);
  for (int iter = 0; iter < 15; iter++) {
    int best_cand = -1;
    double best_min = -1e9;
    for (size_t c = 0; c < zero_defect_dirs.size(); c++) {
      double min_d = 1e9;
      for (size_t p = 0; p < pts.size(); p++) {
        double d = std::max(current_max[p], (double)yocto::dot(pts[p], zero_defect_dirs[c]));
        if (d < min_d) min_d = d;
      }
      if (min_d > best_min) {
        best_min = min_d;
        best_cand = c;
      }
    }
    selected_idx.push_back(best_cand);
    for (size_t p = 0; p < pts.size(); p++) {
      current_max[p] = std::max(current_max[p], (double)yocto::dot(pts[p], zero_defect_dirs[best_cand]));
    }
  }

  double c_comp = 0.0006;
  vec3 v0 = u0 / c_cone;
  std::vector<vec3> v_all;
  v_all.push_back(v0);
  for (int idx : selected_idx) {
    v_all.push_back(zero_defect_dirs[idx] / c_comp);
  }

  // Compute min over unit sphere of max(a . v_j):
  N = 200000;
  double min_cover = 1e9;
  vec3 worst_a = {0, 0, 0};
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double max_d = -1e9;
    for (const auto &v : v_all) {
      double d = yocto::dot(a, v);
      if (d > max_d) max_d = d;
    }
    if (max_d < min_cover) {
      min_cover = max_d;
      worst_a = a;
    }
  }
  std::cout << "Min cover of rescaled 16 axes: " << min_cover << "\n";
  std::cout << "worst_a . u0 = " << yocto::dot(worst_a, u0) << " (c_cone = " << c_cone << ")\n";
  std::cout << "worst_a . v0 = " << yocto::dot(worst_a, v0) << "\n";
  for (size_t k = 0; k < selected_idx.size(); k++) {
    std::cout << "worst_a . comp[" << k << "] = " << yocto::dot(worst_a, zero_defect_dirs[selected_idx[k]])
              << " (scaled = " << yocto::dot(worst_a, zero_defect_dirs[selected_idx[k]]) / c_comp << ")\n";
  }

  return 0;
}
