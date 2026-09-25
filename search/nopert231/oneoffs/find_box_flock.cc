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

struct Box2D {
  double x_min, x_max, y_min, y_max;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                 ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                 ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  double norm_u0 = yocto::length(u0);
  double u0_sq = yocto::length_squared(u0);

  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::normalize(yocto::cross(u0, k1));

  double c_cone = 0.025;
  double c_core = 0.0001;

  // Filter all audited axes that have zero defect:
  struct CandAxis {
    size_t orig_idx;
    vec3 v;
    double c1, c2, coeff0;
  };
  std::vector<CandAxis> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double c1 = yocto::dot(v, k1);
    double c2 = yocto::dot(v, k2);
    double coeff0 = yocto::dot(v, u0) / u0_sq;
    cands.push_back({i, v, c1, c2, coeff0});
  }
  std::cout << "Total candidate axes: " << cands.size() << "\n";

  // Build grid of boxes for G = 4, 6, 8
  for (int G : {3, 4, 5, 6}) {
    double step = 2.0 / G;
    std::vector<Box2D> disk_boxes;

    for (int ix = 0; ix < G; ix++) {
      double x_min = -1.0 + ix * step;
      double x_max = x_min + step;
      for (int iy = 0; iy < G; iy++) {
        double y_min = -1.0 + iy * step;
        double y_max = y_min + step;

        double dx = (x_min > 0) ? x_min : (x_max < 0 ? -x_max : 0.0);
        double dy = (y_min > 0) ? y_min : (y_max < 0 ? -y_max : 0.0);
        if (dx * dx + dy * dy > 1.0 - (c_cone/norm_u0)*(c_cone/norm_u0)) continue;
        disk_boxes.push_back({x_min, x_max, y_min, y_max});
      }
    }

    std::cout << "\nTesting Grid " << G << "x" << G << " with " << disk_boxes.size() << " boxes:\n";

    // Matrix of which axis covers which box:
    std::vector<std::vector<bool>> covers(cands.size(), std::vector<bool>(disk_boxes.size(), false));
    for (size_t i = 0; i < cands.size(); i++) {
      for (size_t b = 0; b < disk_boxes.size(); b++) {
        const auto &bx = disk_boxes[b];
        double corner = (cands[i].c1 >= 0 ? cands[i].c1 * bx.x_min : cands[i].c1 * bx.x_max) +
                        (cands[i].c2 >= 0 ? cands[i].c2 * bx.y_min : cands[i].c2 * bx.y_max) +
                        (cands[i].coeff0 >= 0 ? cands[i].coeff0 * c_cone : cands[i].coeff0 * norm_u0);
        if (corner >= c_core) {
          covers[i][b] = true;
        }
      }
    }

    // Greedy set cover over disk_boxes:
    std::vector<bool> box_covered(disk_boxes.size(), false);
    std::vector<size_t> chosen;
    int covered_count = 0;

    while (covered_count < (int)disk_boxes.size()) {
      int best_axis = -1;
      int best_new = -1;
      for (size_t i = 0; i < cands.size(); i++) {
        int n = 0;
        for (size_t b = 0; b < disk_boxes.size(); b++) {
          if (!box_covered[b] && covers[i][b]) n++;
        }
        if (n > best_new) {
          best_new = n;
          best_axis = i;
        }
      }
      if (best_new <= 0) break;
      chosen.push_back(best_axis);
      for (size_t b = 0; b < disk_boxes.size(); b++) {
        if (!box_covered[b] && covers[best_axis][b]) {
          box_covered[b] = true;
          covered_count++;
        }
      }
    }

    std::cout << "Grid " << G << "x" << G << ": covered " << covered_count << " / " << disk_boxes.size()
              << " boxes using " << chosen.size() << " axes!\n";
    if (covered_count == (int)disk_boxes.size()) {
      std::cout << "SUCCESS! 100% of boxes covered!\n";
      for (size_t m = 0; m < chosen.size(); m++) {
        std::cout << "  Axis " << m << ": cand " << chosen[m] << " (orig " << cands[chosen[m]].orig_idx << ")\n";
      }
      break;
    }
  }

  return 0;
}
