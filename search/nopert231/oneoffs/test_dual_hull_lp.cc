#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;

static inline vec3 VtoD(const BigVecQ3 &v) {
  return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  vec3 tri1_f[3] = {
    VtoD(tri1.corners[0]),
    VtoD(tri1.corners[1]),
    VtoD(tri1.corners[2]),
  };

  vec3 u = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;
  u = u * (1.0 / yocto::length(u));

  // 2D projection basis
  vec3 up = {0, 1, 0};
  if (std::abs(yocto::dot(u, up)) > 0.9) up = {1, 0, 0};
  vec3 ex = yocto::normalize(yocto::cross(u, up));
  vec3 ey = yocto::cross(u, ex);

  // Rotation axis: uncovered direction -sep_norm
  vec3 uncov = {0.401011, -0.483067, -0.778355};

  // Find all strictly valid contacts across tri1
  struct StrictContact {
    ContactInfo ci;
    vec2 normal2d;
    double vel;
    double slack;
  };

  std::vector<StrictContact> contacts;
  for (int v = 0; v < 20; v++) {
    for (int es = 0; es < 20; es++) {
      for (int ef = 0; ef < 20; ef++) {
        if (es == ef) continue;
        for (int mix : {0, 200, 333, 500, 667, 800, 1000}) {
          ContactInfo c = {v, es, ef, es, ef, mix};
          vec3 edge = Tube229::GetDoubleEdge(c);
          bool valid = true;
          double min_slack = 1e30;
          for (int k = 0; k < 20; k++) {
            if (k == v) continue;
            vec3 delta = VtoD(Tube229::VertexQ(k)) - VtoD(Tube229::VertexQ(v));
            vec3 coeff = yocto::cross(edge, delta);
            for (int corner = 0; corner < 3; corner++) {
              double d = yocto::dot(tri1_f[corner], coeff);
              if (d > 0.0) { valid = false; break; }
              min_slack = std::min(min_slack, -d);
            }
            if (!valid) break;
          }
          if (valid && min_slack > 1e-6) {
            vec3 n3 = yocto::cross(u, edge);
            vec2 n2 = {yocto::dot(n3, ex), yocto::dot(n3, ey)};
            double len = std::sqrt(n2.x*n2.x + n2.y*n2.y);
            if (len > 1e-10) {
              n2 = {n2.x / len, n2.y / len};
              vec3 v3 = VtoD(Tube229::VertexQ(v));
              vec3 vel3 = yocto::cross(uncov, v3);
              vec2 vel2 = {yocto::dot(vel3, ex), yocto::dot(vel3, ey)};
              double normal_vel = n2.x * vel2.x + n2.y * vel2.y;
              contacts.push_back({c, n2, normal_vel, min_slack});
            }
          }
        }
      }
    }
  }

  std::cout << "Found " << contacts.size() << " strictly valid contacts.\n";

  double best_obj = -1e30;
  int best_triple[3] = {-1, -1, -1};
  double best_lambda[3] = {0, 0, 0};

  int N = contacts.size();
  for (int i = 0; i < N; i++) {
    for (int j = i + 1; j < N; j++) {
      for (int k = j + 1; k < N; k++) {
        vec2 ni = contacts[i].normal2d;
        vec2 nj = contacts[j].normal2d;
        vec2 nk = contacts[k].normal2d;

        double det = ni.x * (nj.y - nk.y) + nj.x * (nk.y - ni.y) + nk.x * (ni.y - nj.y);
        if (std::abs(det) < 1e-9) continue;

        double l0 = (nj.x * nk.y - nj.y * nk.x) / det;
        double l1 = (nk.x * ni.y - nk.y * ni.x) / det;
        double l2 = (ni.x * nj.y - ni.y * nj.x) / det;

        if (l0 > 1e-6 && l1 > 1e-6 && l2 > 1e-6) {
          double obj = l0 * contacts[i].vel + l1 * contacts[j].vel + l2 * contacts[k].vel;
          if (obj > best_obj) {
            best_obj = obj;
            best_triple[0] = i; best_triple[1] = j; best_triple[2] = k;
            best_lambda[0] = l0; best_lambda[1] = l1; best_lambda[2] = l2;
          }
        }
      }
    }
  }

  std::cout << std::setprecision(10);
  std::cout << "Optimal dual value over strictly valid contacts: " << best_obj << "\n";
  if (best_obj > -1e20) {
    std::cout << "Strictly balanced combination found!\n";
    for (int m = 0; m < 3; m++) {
      int idx = best_triple[m];
      std::cout << "  Contact " << m << ": lambda = " << best_lambda[m]
                << ", vertex = " << contacts[idx].ci.vertex
                << ", edge = (" << contacts[idx].ci.edge_start << "->" << contacts[idx].ci.edge_finish << ")"
                << ", mix = " << contacts[idx].ci.mix
                << ", normal_vel = " << contacts[idx].vel
                << ", slack = " << contacts[idx].slack << "\n";
    }
  }

  return 0;
}
