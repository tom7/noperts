#include <iostream>
#include <vector>
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

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return a.x * (b.y * c.z - b.z * c.y) -
         a.y * (b.x * c.z - b.z * c.x) +
         a.z * (b.x * c.y - b.y * c.x);
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Annular axis u0:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000))) return 1;
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

  std::vector<int> std_mixes = {0, 200, 333, 400, 500, 600, 666, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  auto candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);

  struct AxisInfo {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    vec3 u;
    vec3 dir;
    double len;
  };

  std::vector<AxisInfo> zero_defect_axes;
  for (size_t i = 0; i < candidates.size(); i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, candidates[i].contacts, &ax, &ctr, &del, &err, BigRat(0))) {
      AxisInfo ai;
      for (int k = 0; k < 3; k++) ai.contacts[k] = candidates[i].contacts[k];
      ai.cert = ax; ai.center = ctr; ai.delta = del;
      ai.u = {ctr.x.ToDouble() / ax.B.ToDouble(),
              ctr.y.ToDouble() / ax.B.ToDouble(),
              ctr.z.ToDouble() / ax.B.ToDouble()};
      ai.len = yocto::length(ai.u);
      ai.dir = ai.u / ai.len;
      zero_defect_axes.push_back(ai);
    }
  }

  // Filter to diverse directions with threshold 0.985
  std::vector<AxisInfo> diverse;
  for (const auto &ax : zero_defect_axes) {
    bool dup = false;
    for (const auto &ex : diverse) {
      if (yocto::dot(ex.dir, ax.dir) > 0.985) { dup = true; break; }
    }
    if (!dup) diverse.push_back(ax);
  }
  std::cout << "Filtered to " << diverse.size() << " diverse axes.\n";

  vec3 oct[6] = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  // Check c_cone = 0.0395, 0.0390, 0.0388, 0.0386:
  for (double c_cone : {0.0395, 0.0390, 0.0388, 0.0386, 0.0380, 0.0350, 0.0300, 0.0250, 0.0200}) {
    for (double c_val : {0.0001, 0.0003, 0.0005}) {
      double delta = del0.ToDouble();
      double scale_0 = (c_val + delta) / c_cone;
      vec3 p0 = scale_0 * u0;
      double target_scale = 1.75 * (c_val + delta);

      for (size_t i = 0; i < diverse.size(); i++) {
        vec3 u1 = diverse[i].u;
        for (size_t j = i + 1; j < diverse.size(); j++) {
          vec3 u2 = diverse[j].u;
          for (size_t k = j + 1; k < diverse.size(); k++) {
            vec3 u3 = diverse[k].u;

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

            bool all_inside = true;
            for (int m = 0; m < 6; m++) {
              vec3 y = target_scale * oct[m] - u3;
              double l0 = Det3(y, b, d) / det;
              double l1 = Det3(a, y, d) / det;
              double l2 = Det3(a, b, y) / det;
              double l3 = 1.0 - l0 - l1 - l2;
              if (l0 <= 0 || l1 <= 0 || l2 <= 0 || l3 <= 0) { all_inside = false; break; }
            }

            if (all_inside) {
              std::cout << "SUCCESS at c_cone = " << c_cone << ", c = " << c_val
                        << " with axes (" << i << ", " << j << ", " << k << ")!\n";
              std::cout << "u1 contacts: [" << diverse[i].contacts[0].edge_start << "->" << diverse[i].contacts[0].edge_finish << "], "
                        << "[" << diverse[i].contacts[1].edge_start << "->" << diverse[i].contacts[1].edge_finish << "], "
                        << "[" << diverse[i].contacts[2].edge_start << "->" << diverse[i].contacts[2].edge_finish << "]\n";
              std::cout << "u2 contacts: [" << diverse[j].contacts[0].edge_start << "->" << diverse[j].contacts[0].edge_finish << "], "
                        << "[" << diverse[j].contacts[1].edge_start << "->" << diverse[j].contacts[1].edge_finish << "], "
                        << "[" << diverse[j].contacts[2].edge_start << "->" << diverse[j].contacts[2].edge_finish << "]\n";
              std::cout << "u3 contacts: [" << diverse[k].contacts[0].edge_start << "->" << diverse[k].contacts[0].edge_finish << "], "
                        << "[" << diverse[k].contacts[1].edge_start << "->" << diverse[k].contacts[1].edge_finish << "], "
                        << "[" << diverse[k].contacts[2].edge_start << "->" << diverse[k].contacts[2].edge_finish << "]\n";
              return 0;
            }
          }
        }
      }
    }
  }

  std::cout << "No cage found in diverse axes.\n";
  return 0;
}
