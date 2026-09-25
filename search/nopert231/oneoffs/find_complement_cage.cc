#include <iostream>
#include <vector>
#include <string>
#include <cmath>
#include <algorithm>
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

static double Det3(vec3 a, vec3 b, vec3 c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Annular axis u0 = zero-defect axis at mix 900
  ContactInfo cts0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 900, 15)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, cts0, &ax0, &ctr0, &del0, &err, BigRat(0))) {
    std::cerr << "Failed to audit u0: " << err << "\n";
    return 1;
  }
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), ||u0|| = " << yocto::length(u0)
            << ", delta = " << del0.ToDouble() << "\n";
  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  // Let us sample contacts across centroid and all 3 corners
  std::vector<ContactInfo> contacts;
  std::vector<int> std_mixes = {0, 200, 400, 600, 800, 1000};
  for (vec3 pt : {centroid, tri_f[0], tri_f[1], tri_f[2]}) {
    auto c_pt = Tube229::GenerateSilhouetteContacts(pt, std_mixes);
    for (const auto &c : c_pt) {
      bool exists = false;
      for (const auto &ex : contacts) {
        if (ex.vertex == c.vertex && ex.edge_start == c.edge_start && ex.edge_finish == c.edge_finish &&
            ex.edge_start2 == c.edge_start2 && ex.edge_finish2 == c.edge_finish2 && ex.mix == c.mix) {
          exists = true; break;
        }
      }
      if (!exists) contacts.push_back(c);
    }
  }

  std::cout << "Total distinct contacts: " << contacts.size() << "\n";
  auto raw_candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);
  std::cout << "Total raw candidates: " << raw_candidates.size() << "\n";

  struct AxisData {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    vec3 u;
    vec3 dir;
  };
  std::vector<AxisData> valid_axes;

  for (const auto &cand : raw_candidates) {
    AxisData ad;
    for (int k = 0; k < 3; k++) ad.contacts[k] = cand.contacts[k];
    if (Tube229::AuditAxis(tri, ad.contacts, &ad.cert, &ad.center, &ad.delta, &err, BigRat(0))) {
      ad.u = {ad.center.x.ToDouble() / ad.cert.B.ToDouble(),
              ad.center.y.ToDouble() / ad.cert.B.ToDouble(),
              ad.center.z.ToDouble() / ad.cert.B.ToDouble()};
      ad.dir = yocto::normalize(ad.u);

      // Only keep diverse axes:
      bool dup = false;
      for (const auto &ex : valid_axes) {
        if (yocto::dot(ex.dir, ad.dir) > 0.95) { dup = true; break; }
      }
      if (!dup) valid_axes.push_back(ad);
    }
  }

  std::cout << "Filtered to " << valid_axes.size() << " diverse valid axes.\n";

  vec3 oct[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  double max_c_cone_found = 0;
  int best_i = -1, best_j = -1, best_k = -1;
  double best_c_val = 0;
  double best_min_bary = 0;

  for (double c_cone = 0.020; c_cone >= 0.002; c_cone -= 0.001) {
    for (double c_val : {0.0001, 0.0003, 0.0005, 0.001}) {
      double delta = del0.ToDouble();
      double scale_0 = (c_val + delta) / c_cone;
      vec3 p0 = scale_0 * u0;
      double target_scale = 1.75 * (c_val + delta);

      for (size_t i = 0; i < valid_axes.size(); i++) {
        vec3 u1 = valid_axes[i].u;
        for (size_t j = i + 1; j < valid_axes.size(); j++) {
          vec3 u2 = valid_axes[j].u;
          for (size_t k = j + 1; k < valid_axes.size(); k++) {
            vec3 u3 = valid_axes[k].u;

            vec3 a = p0 - u3;
            vec3 b = u1 - u3;
            vec3 d = u2 - u3;
            double det = Det3(a, b, d);
            if (std::abs(det) < 1e-15) continue;

            vec3 y0 = -u3;
            double o0 = Det3(y0, b, d) / det;
            double o1 = Det3(a, y0, d) / det;
            double o2 = Det3(a, b, y0) / det;
            double o3 = 1.0 - o0 - o1 - o2;
            if (o0 <= 0 || o1 <= 0 || o2 <= 0 || o3 <= 0) continue;

            // Origin is inside!
            int neg_count = 0;
            double worst_coord = 1.0;
            for (int m = 0; m < 6; m++) {
              vec3 y = target_scale * oct[m] - u3;
              double l0 = Det3(y, b, d) / det;
              double l1 = Det3(a, y, d) / det;
              double l2 = Det3(a, b, y) / det;
              double l3 = 1.0 - l0 - l1 - l2;
              double mb = std::min({l0, l1, l2, l3});
              if (mb < worst_coord) worst_coord = mb;
              if (mb <= 0) neg_count++;
            }
            if (neg_count == 0) {
              std::cout << "SUCCESS at c_cone = " << c_cone << ", c = " << c_val << " with axes (" << i << ", " << j << ", " << k << ")\n";
              return 0;
            }

            bool all_inside = true;
            double min_bary = std::min({o0, o1, o2, o3});
            for (int m = 0; m < 6; m++) {
              vec3 y = target_scale * oct[m] - u3;
              double l0 = Det3(y, b, d) / det;
              double l1 = Det3(a, y, d) / det;
              double l2 = Det3(a, b, y) / det;
              double l3 = 1.0 - l0 - l1 - l2;
              double mb = std::min({l0, l1, l2, l3});
              if (mb < min_bary) min_bary = mb;
              if (mb <= 0) { all_inside = false; break; }
            }

            if (all_inside) {
              if (c_cone > max_c_cone_found) {
                max_c_cone_found = c_cone;
                best_i = i; best_j = j; best_k = k;
                best_c_val = c_val;
                best_min_bary = min_bary;
                std::cout << "NEW MAX c_cone = " << c_cone << " (c = " << c_val << ", min_bary = " << min_bary << ") with axes (" << i << ", " << j << ", " << k << ")\n";
              }
            }
          }
        }
      }
    }
  }

  std::cout << "Overall max c_cone found: " << max_c_cone_found << "\n";
  if (best_i >= 0) {
    std::cout << "Winning axes contacts:\n";
    for (int idx : {best_i, best_j, best_k}) {
      std::cout << "  Axis " << idx << ":\n";
      for (int m = 0; m < 3; m++) {
        const auto &ct = valid_axes[idx].contacts[m];
        std::cout << "    MakeContact(" << ct.edge_start << ", " << ct.edge_finish << ", " << ct.edge_start2 << ", " << ct.edge_finish2 << ", " << ct.mix << ", " << ct.vertex << "),\n";
      }
    }
  }
  return 0;
}
