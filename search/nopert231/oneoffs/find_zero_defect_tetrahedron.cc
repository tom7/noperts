#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
  };

  std::vector<Axis> zero_defect_axes;
  std::string err;

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
          a.cQ = cQ;
          a.delta = delta;
          a.cert = ax;
          zero_defect_axes.push_back(a);
        }
      }
    }
  }

  std::cout << "Audited " << zero_defect_axes.size() << " zero-defect axes.\n";

  // Cluster axes by unit direction to get ~100 distinct directions
  std::vector<Axis> unique_axes;
  for (const auto &ax : zero_defect_axes) {
    vec3 u = yocto::normalize(ax.c);
    bool duplicate = false;
    for (const auto &uax : unique_axes) {
      if (yocto::dot(u, yocto::normalize(uax.c)) > 0.99) {
        duplicate = true;
        break;
      }
    }
    if (!duplicate) {
      unique_axes.push_back(ax);
    }
  }
  std::cout << "Clustered into " << unique_axes.size() << " distinct directions.\n";

  // Precompute 1000 Fibonacci sphere points
  int N = 1000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  // Search 4-tuples of unique axes that contain origin with positive margin
  int U = unique_axes.size();
  std::cout << "Searching 4-tuples among " << U << " distinct axes...\n";

  double best_inradius = -999.0;
  int best_idx[4] = {-1, -1, -1, -1};

  for (int i0 = 0; i0 < U; i0++) {
    for (int i1 = i0 + 1; i1 < U; i1++) {
      for (int i2 = i1 + 1; i2 < U; i2++) {
        // Fast test: is origin on the negative side of face (0, 1, 2)?
        vec3 n012 = yocto::cross(unique_axes[i1].c - unique_axes[i0].c,
                                 unique_axes[i2].c - unique_axes[i0].c);
        // We need origin to be on one side, and the 4th vertex on the other
        for (int i3 = i2 + 1; i3 < U; i3++) {
          const vec3 &v0 = unique_axes[i0].c;
          const vec3 &v1 = unique_axes[i1].c;
          const vec3 &v2 = unique_axes[i2].c;
          const vec3 &v3 = unique_axes[i3].c;

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

          if (b0 > 0.02 && b1 > 0.02 && b2 > 0.02 && b3 > 0.02) {
            // Origin is strictly inside! Compute inradius on sphere:
            double min_c = 999.0;
            for (int s = 0; s < N; s++) {
              double d = std::max({yocto::dot(pts[s], v0), yocto::dot(pts[s], v1),
                                   yocto::dot(pts[s], v2), yocto::dot(pts[s], v3)});
              if (d < min_c) min_c = d;
            }
            if (min_c > best_inradius) {
              best_inradius = min_c;
              best_idx[0] = i0; best_idx[1] = i1; best_idx[2] = i2; best_idx[3] = i3;
              std::cout << "Found cage! inradius = " << min_c << ", b = ("
                        << b0 << ", " << b1 << ", " << b2 << ", " << b3 << ")\n";
              if (min_c > 0.001) goto done;
            }
          }
        }
      }
    }
  }

done:
  if (best_inradius > 0) {
    std::cout << "SUCCESS! Best inradius = " << best_inradius << "\n";
    std::cout << "Axes: " << best_idx[0] << ", " << best_idx[1] << ", "
              << best_idx[2] << ", " << best_idx[3] << "\n";
    for (int m = 0; m < 4; m++) {
      const auto &ax = unique_axes[best_idx[m]];
      std::cout << "Axis " << m << ": center = (" << ax.c.x << ", " << ax.c.y << ", " << ax.c.z << "), delta = " << ax.delta.ToDouble() << "\n";
    }
  } else {
    std::cout << "No strictly enclosing 4-simplex found.\n";
  }

  return 0;
}
