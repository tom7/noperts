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

  // Axis 0:
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

  // Core axis:
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &center_core, &delta_core, &err, BigRat(0));
  vec3 v_core = {center_core.x.ToDouble() / ax_core.B.ToDouble(),
                 center_core.y.ToDouble() / ax_core.B.ToDouble(),
                 center_core.z.ToDouble() / ax_core.B.ToDouble()};

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ") len=" << yocto::length(u0) << "\n";
  std::cout << "v_core: (" << v_core.x << ", " << v_core.y << ", " << v_core.z << ") len=" << yocto::length(v_core) << "\n";

  // Generate all zero-defect candidate axes:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 200, 333, 400, 500, 600, 667, 800, 1000}) {
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
  std::vector<vec3> zero_defect_axes;
  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          vec3 v = {center.x.ToDouble() / ax.B.ToDouble(),
                    center.y.ToDouble() / ax.B.ToDouble(),
                    center.z.ToDouble() / ax.B.ToDouble()};
          zero_defect_axes.push_back(v);
        }
      }
    }
  }
  std::cout << "Total zero-defect axes generated: " << zero_defect_axes.size() << "\n";

  // Start with 3 complement axes:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<vec3> selected_comps = {
    vec3{axes500[421].center.x.ToDouble() / axes500[421].cert.B.ToDouble(),
         axes500[421].center.y.ToDouble() / axes500[421].cert.B.ToDouble(),
         axes500[421].center.z.ToDouble() / axes500[421].cert.B.ToDouble()},
    vec3{axes500[264].center.x.ToDouble() / axes500[264].cert.B.ToDouble(),
         axes500[264].center.y.ToDouble() / axes500[264].cert.B.ToDouble(),
         axes500[264].center.z.ToDouble() / axes500[264].cert.B.ToDouble()},
    vec3{axes500[428].center.x.ToDouble() / axes500[428].cert.B.ToDouble(),
         axes500[428].center.y.ToDouble() / axes500[428].cert.B.ToDouble(),
         axes500[428].center.z.ToDouble() / axes500[428].cert.B.ToDouble()}
  };

  // Test on sphere:
  int N = 100000;
  std::vector<vec3> sphere_pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    sphere_pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  double c_margin = 0.005;

  // Greedily add zero-defect axes that maximize the minimum of dot(a, v_core) on the fail set:
  for (int round = 0; round < 10; round++) {
    // Find current fail set:
    std::vector<vec3> fail_pts;
    double min_u0 = 1e9, min_core = 1e9;
    for (const auto &a : sphere_pts) {
      bool covered = false;
      for (const auto &comp : selected_comps) {
        if (yocto::dot(a, comp) >= c_margin) {
          covered = true;
          break;
        }
      }
      if (!covered) {
        fail_pts.push_back(a);
        min_u0 = std::min(min_u0, yocto::dot(a, u0));
        min_core = std::min(min_core, yocto::dot(a, v_core));
      }
    }

    std::cout << "Round " << round << ": comps=" << selected_comps.size()
              << ", fail_pts=" << fail_pts.size()
              << ", min_u0=" << min_u0
              << ", min_core=" << min_core << "\n";

    if (min_core >= 0.0005) {
      std::cout << "SUCCESS! min_core = " << min_core << " >= 0.0005 and min_u0 = " << min_u0 << " >= 0.005!\n";
      break;
    }

    // Pick best zero-defect axis to eliminate the remaining fail points:
    int best_ax = -1;
    int max_elim = 0;
    double best_score = -1e9;
    for (size_t ax = 0; ax < zero_defect_axes.size(); ax++) {
      int elim = 0;
      double cur_min_core = 1e9;
      for (const auto &a : fail_pts) {
        if (yocto::dot(a, zero_defect_axes[ax]) >= c_margin) {
          elim++;
        } else {
          cur_min_core = std::min(cur_min_core, yocto::dot(a, v_core));
        }
      }
      if (elim > max_elim || (elim == max_elim && cur_min_core > best_score)) {
        max_elim = elim;
        best_score = cur_min_core;
        best_ax = ax;
      }
    }

    std::cout << "  Adding axis " << best_ax << " which eliminates " << max_elim << " points\n";
    if (best_ax >= 0 && max_elim > 0) {
      selected_comps.push_back(zero_defect_axes[best_ax]);
    } else {
      break;
    }
  }


  return 0;
}
