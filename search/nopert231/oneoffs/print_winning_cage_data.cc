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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 100000000));
  vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};

  std::vector<ContactInfo> contacts;
  for (int mix : {0, 200, 333, 500, 666, 800, 1000}) {
    contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    contacts.push_back(MakeContact(19, 3, 3, 2, mix, 3));
    contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  struct Axis {
    vec3 c;
    BigVecQ3 cQ;
    BigRat delta;
    AxisCertificate cert;
    ContactInfo triple[3];
  };
  std::vector<Axis> zero_axes;

  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo triple[3] = {contacts[i], contacts[j], contacts[k]};
        AxisCertificate ax;
        BigVecQ3 cQ;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &ax, &cQ, &delta, &err, BigRat(0))) {
          Axis a;
          a.c = {cQ.x.ToDouble(), cQ.y.ToDouble(), cQ.z.ToDouble()};
          a.cQ = cQ; a.delta = delta; a.cert = ax;
          a.triple[0] = contacts[i]; a.triple[1] = contacts[j]; a.triple[2] = contacts[k];
          zero_axes.push_back(a);
        }
      }
    }
  }

  std::vector<Axis> unique;
  for (const auto &ax : zero_axes) {
    vec3 u = yocto::normalize(ax.c);
    bool dup = false;
    for (const auto &uax : unique) {
      if (yocto::dot(u, yocto::normalize(uax.c)) > 0.98) {
        dup = true; break;
      }
    }
    if (!dup) unique.push_back(ax);
  }

  double c_cone = 0.045;
  double c_val = 0.0002;
  vec3 v0 = (c_val / c_cone) * u0;

  int N = 1000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  int U = unique.size();
  double best_margin = -999.0;
  int best_tri[3] = {-1, -1, -1};

  for (int i1 = 0; i1 < U; i1++) {
    for (int i2 = i1 + 1; i2 < U; i2++) {
      for (int i3 = i2 + 1; i3 < U; i3++) {
        const vec3 &v1 = unique[i1].c;
        const vec3 &v2 = unique[i2].c;
        const vec3 &v3 = unique[i3].c;

        double d0 = -yocto::dot(v1, yocto::cross(v2, v3));
        double d1 =  yocto::dot(v0, yocto::cross(v2, v3));
        double d2 = -yocto::dot(v0, yocto::cross(v1, v3));
        double d3 =  yocto::dot(v0, yocto::cross(v1, v2));
        double det = d0 + d1 + d2 + d3;
        if (std::abs(det) < 1e-12) continue;

        double b0 = d0 / det;
        double b1 = d1 / det;
        double b2 = d2 / det;
        double b3 = d3 / det;

        if (b0 > 0.001 && b1 > 0.001 && b2 > 0.001 && b3 > 0.001) {
          double min_c = 999.0;
          for (int s = 0; s < N; s++) {
            double d = std::max({yocto::dot(pts[s], v0), yocto::dot(pts[s], v1),
                                 yocto::dot(pts[s], v2), yocto::dot(pts[s], v3)});
            if (d < min_c) min_c = d;
          }
          if (min_c > best_margin) {
            best_margin = min_c;
            best_tri[0] = i1; best_tri[1] = i2; best_tri[2] = i3;
          }
        }
      }
    }
  }

  std::cout << "WINNING CAGE FOUND! Margin = " << best_margin << "\n";
  for (int m = 0; m < 3; m++) {
    const auto &ax = unique[best_tri[m]];
    std::cout << "Axis " << m + 1 << ": delta = " << ax.delta.ToString() << "\n";
    for (int c = 0; c < 3; c++) {
      std::cout << "  contact " << c << ": ("
                << ax.triple[c].edge_start << "->" << ax.triple[c].edge_finish
                << ", " << ax.triple[c].edge_start2 << "->" << ax.triple[c].edge_finish2
                << ", mix " << ax.triple[c].mix << ", v " << ax.triple[c].vertex << ")\n";
    }
  }

  return 0;
}
