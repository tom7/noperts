#include <iostream>
#include <vector>
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

  ContactInfo core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  std::string err;
  Tube229::AuditAxis(tri, core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  vec3 v_core = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.z.ToDouble() / ax_core.B.ToDouble()};

  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<vec3> pool;
  for (const auto &ax : axes500) {
    pool.push_back({ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                    ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                    ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  // Can we find 3 axes from pool such that {v_core, a1, a2, a3} encloses 0?
  // Let's use greedy search:
  int N = 50000;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts.push_back({(float)(r * std::cos(phi)), (float)(r * std::sin(phi)), (float)z});
  }

  std::vector<int> selected;
  std::vector<double> max_dots(N);
  for (int i = 0; i < N; i++) {
    max_dots[i] = yocto::dot(pts[i], v_core);
  }

  for (int step = 0; step < 12; step++) {
    double min_dot = 1e9;
    int worst_pt = -1;
    for (int i = 0; i < N; i++) {
      if (max_dots[i] < min_dot) {
        min_dot = max_dots[i];
        worst_pt = i;
      }
    }
    std::cout << "Step " << step << ": inradius = " << min_dot << "\n";
    int best_c = -1;
    double best_val = -1e9;
    for (size_t c = 0; c < pool.size(); c++) {
      double d = yocto::dot(pts[worst_pt], pool[c]);
      if (d > best_val) {
        best_val = d;
        best_c = c;
      }
    }
    if (best_c == -1) break;
    selected.push_back(best_c);
    for (int i = 0; i < N; i++) {
      double d = yocto::dot(pts[i], pool[best_c]);
      if (d > max_dots[i]) max_dots[i] = d;
    }
  }

  return 0;
}
