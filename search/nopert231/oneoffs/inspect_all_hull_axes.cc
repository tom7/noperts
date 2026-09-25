#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "nopert229.h"
#include "geom/hull-2d.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

using vec2 = yocto::vec<double, 2>;

static vec3 ToD(const BigVecQ3 &v) {
  return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));
  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  vec3 c0 = ToD(tri.corners[0]);
  vec3 c1 = ToD(tri.corners[1]);
  vec3 c2 = ToD(tri.corners[2]);
  vec3 centroid = (c0 + c1 + c2) * (1.0 / 3.0);
  double vlen = yocto::length(centroid);
  // LOOK FROM OPPOSITE SIDE (-centroid):
  vec3 unit_view = -centroid / vlen;

  int axis_index = 0;
  double min_abs = 2.0;
  for (int i = 0; i < 3; i++) {
    if (std::abs(unit_view[i]) < min_abs) {
      min_abs = std::abs(unit_view[i]);
      axis_index = i;
    }
  }
  vec3 axis = (axis_index == 0 ? vec3{1, 0, 0} : (axis_index == 1 ? vec3{0, 1, 0} : vec3{0, 0, 1}));
  vec3 first = yocto::normalize(yocto::cross(unit_view, axis));
  vec3 second = yocto::cross(unit_view, first);

  std::vector<vec2> projected(24);
  for (int k = 0; k < 24; k++) {
    projected[k] = vec2{yocto::dot(::Vertex(k), first), yocto::dot(::Vertex(k), second)};
  }
  std::vector<int> hull = Tube229::ConvexHull2D(projected);
  std::set<int> hull_vertices(hull.begin(), hull.end());

  std::vector<int> mixes = {0, 200, 333, 500, 666, 800, 1000};
  std::vector<ContactInfo> candidate_contacts;
  int H = hull.size();

  for (int pos = 0; pos < H; pos++) {
    int v = hull[pos];
    int prev = hull[(pos - 1 + H) % H];
    int next = hull[(pos + 1) % H];
    for (int mix : mixes) {
      ContactInfo ci;
      ci.vertex = v;
      ci.edge_start = prev;
      ci.edge_finish = v;
      ci.edge_start2 = v;
      ci.edge_finish2 = next;
      ci.mix = mix;
      candidate_contacts.push_back(ci);
    }
  }

  std::vector<ContactInfo> std_contacts = Tube229::GenerateSilhouetteContacts(centroid, mixes);
  for (const auto &c : std_contacts) {
    if (hull_vertices.count(c.vertex)) candidate_contacts.push_back(c);
  }

  vec3 tri_f[3] = {c0, c1, c2};
  std::vector<ContactInfo> valid_contacts;
  for (const auto &c : candidate_contacts) {
    vec3 edge = Tube229::GetDoubleEdge(c);
    int sel = c.vertex;
    bool ok = true;
    for (int k = 0; k < 24; k++) {
      bool tie = (k == sel) ||
                 (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta_v = ::Vertex(k) - ::Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta_v);
      double u0_val = yocto::dot(tri_f[0], coeff);
      double u1_val = yocto::dot(tri_f[1], coeff);
      double u2_val = yocto::dot(tri_f[2], coeff);
      if (std::max({u0_val, u1_val, u2_val}) > 1e-12) {
        ok = false;
        break;
      }
    }
    if (ok) valid_contacts.push_back(c);
  }

  std::cout << "Valid contacts from -unit_view: " << valid_contacts.size() << "\n";
  double max_dot = -1.0;
  ContactInfo best_triple[3];
  AxisCertificate best_cert;
  BigVecQ3 best_ctr;
  BigRat best_del;

  for (size_t i = 0; i < valid_contacts.size(); i++) {
    for (size_t j = i + 1; j < valid_contacts.size(); j++) {
      for (size_t k = j + 1; k < valid_contacts.size(); k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        Tube229::CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        AxisCertificate exact_cert;
        BigVecQ3 center;
        BigRat delta;
        std::string fail;
        if (Tube229::AuditAxis(tri, triple, &exact_cert, &center, &delta, &fail, BigRat(0))) {
          vec3 uc = {center.x.ToDouble() / exact_cert.B.ToDouble(),
                     center.y.ToDouble() / exact_cert.B.ToDouble(),
                     center.z.ToDouble() / exact_cert.B.ToDouble()};
          double dot_unit = yocto::dot(u0_dir, yocto::normalize(uc));
          if (dot_unit > max_dot) {
            max_dot = dot_unit;
            best_cert = exact_cert;
            best_ctr = center;
            best_del = delta;
            for (int m = 0; m < 3; m++) best_triple[m] = triple[m];
            double ang = std::acos(std::clamp(max_dot, -1.0, 1.0)) * 180.0 / M_PI;
            std::cout << "NEW BEST AXIS: max_dot=" << max_dot << ", angle=" << ang << " deg, B=" << exact_cert.B.ToDouble() << "\n";
            for (int m = 0; m < 3; m++) {
              std::cout << "  c[" << m << "]: (" << best_triple[m].edge_start << "->" << best_triple[m].edge_finish
                        << ", " << best_triple[m].edge_start2 << "->" << best_triple[m].edge_finish2
                        << ", mix=" << best_triple[m].mix << ", v=" << best_triple[m].vertex << ")\n";
            }
          }
        }
      }
    }
  }

  std::cout << "SEARCH FINISHED. Global max_dot = " << max_dot << "\n";
  return 0;
}
