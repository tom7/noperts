#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 Vert(int k) {
  BigVecQ3 v = Tube229::VertexQ(k);
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 tri_f[3] = {
    vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()},
    vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()},
    vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()}
  };

  std::string err;
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c_cone = 0.2; // 1/5

  // Collect valid contact pairs across multiple vertices:
  // To keep it fast, test actual edge-adjacent vertex pairs from Polyhedron #229:
  std::vector<ContactInfo> valid_contacts;
  for (int v = 0; v < 22; v++) {
    for (int u = 0; u < 22; u++) {
      if (u == v) continue;
      for (int w = 0; w < 22; w++) {
        if (w == v || w == u) continue;

        // Only test vertices that have small dot with u0 or are active
        for (int mix : {0, 200, 500, 800, 1000}) {
          ContactInfo c;
          c.vertex = v;
          c.edge_start = u; c.edge_finish = v;
          c.edge_start2 = v; c.edge_finish2 = w;
          c.mix = mix;

          vec3 edge = Tube229::GetDoubleEdge(c);
          if (yocto::length(edge) < 1e-6) continue;

          bool ok = true;
          for (int k = 0; k < 22; k++) {
            bool tie = (k == v) ||
                       (mix == 1000 && v == c.edge_finish && k == c.edge_start) ||
                       (mix == 0 && v == c.edge_start2 && k == c.edge_finish2);
            if (tie) continue;
            vec3 delta_v = Vert(k) - Vert(v);
            vec3 coeff = yocto::cross(edge, delta_v);
            double u0_val = yocto::dot(tri_f[0], coeff);
            double u1_val = yocto::dot(tri_f[1], coeff);
            double u2_val = yocto::dot(tri_f[2], coeff);
            if (std::max({u0_val, u1_val, u2_val}) > 1e-12) {
              ok = false;
              break;
            }
          }
          if (ok) {
            valid_contacts.push_back(c);
          }
        }
      }
    }
  }

  std::cout << "Valid contacts: " << valid_contacts.size() << "\n";

  // Filter to unique edge directions to avoid redundancy:
  std::vector<ContactInfo> filtered_contacts;
  for (const auto &c : valid_contacts) {
    vec3 e = yocto::normalize(Tube229::GetDoubleEdge(c));
    bool dup = false;
    for (const auto &fc : filtered_contacts) {
      if (fc.vertex == c.vertex) {
        vec3 fe = yocto::normalize(Tube229::GetDoubleEdge(fc));
        if (yocto::length(e - fe) < 1e-3) {
          dup = true; break;
        }
      }
    }
    if (!dup) filtered_contacts.push_back(c);
  }
  std::cout << "Filtered distinct contacts: " << filtered_contacts.size() << "\n";

  std::vector<vec3> zero_axes;
  for (size_t i = 0; i < filtered_contacts.size(); i++) {
    for (size_t j = i + 1; j < filtered_contacts.size(); j++) {
      for (size_t k = j + 1; k < filtered_contacts.size(); k++) {
        ContactInfo triple[3] = {filtered_contacts[i], filtered_contacts[j], filtered_contacts[k]};
        Tube229::CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        AxisCertificate cert;
        BigVecQ3 center;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &err, BigRat(0))) {
          vec3 a = yocto::normalize(vec3{center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
          zero_axes.push_back(a);
          if (zero_axes.size() >= 50000) goto done_audit;
        }
      }
    }
  }
done_audit:
  std::cout << "Audited zero axes: " << zero_axes.size() << "\n";

  // Check cone coverage with 100,000 points:
  double c_core_target = 0.001;
  int N = 100000;
  int uncovered = 0;
  double min_max_dot = 1e9;
  for (int i = 0; i < N; i++) {
    double z = c_cone + (1.0 - c_cone) * (double)i / (double)N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 local_pt = {r * std::cos(phi), r * std::sin(phi), z};
    vec3 up = std::abs(u0.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0};
    vec3 e1 = yocto::normalize(yocto::cross(u0, up));
    vec3 e2 = yocto::cross(u0, e1);
    vec3 a = yocto::normalize(local_pt.x * e1 + local_pt.y * e2 + local_pt.z * u0);

    double max_dot = -1e9;
    for (const auto &v : zero_axes) {
      double d = yocto::dot(a, v);
      if (d > max_dot) max_dot = d;
      if (max_dot >= c_core_target) break;
    }
    if (max_dot < min_max_dot) min_max_dot = max_dot;
    if (max_dot < c_core_target) {
      uncovered++;
    }
  }

  std::cout << "Target c_core = " << c_core_target << "\n";
  std::cout << "Uncovered points in cone: " << uncovered << " / " << N << "\n";
  std::cout << "Minimum max dot across all sampled cone points: " << min_max_dot << "\n";

  return 0;
}
