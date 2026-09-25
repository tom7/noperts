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

static bool SolveTetraPoint(const vec3& p0, const vec3& p1,
                            const vec3& p2, const vec3& p3,
                            const vec3& target,
                            double w[4]) {
  double M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  double rhs[3] = {target.x - p3.x, target.y - p3.y, target.z - p3.z};

  double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (std::abs(det) < 1e-12) return false;

  double d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  double d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  double d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = 1.0 - w[0] - w[1] - w[2];
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  std::cout << "Auditing zero-defect Axis 0...\n";
  // We use our zero-defect Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0))) {
    std::cout << "Axis 0 audit failed: " << err << "\n";
    return 1;
  }
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "Finding hull support axes...\n";
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Found " << base_axes.size() << " hull support axes.\n";

  // Filter to ~250 diverse directions:
  struct FilteredAxis {
    size_t orig_idx;
    vec3 u;
  };
  std::vector<FilteredAxis> filtered;
  for (size_t i = 0; i < base_axes.size(); i++) {
    vec3 u = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
              base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
              base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
    bool keep = true;
    for (const auto& f : filtered) {
      if (yocto::dot(u, f.u) / (yocto::length(u) * yocto::length(f.u)) > std::cos(3.0 * M_PI / 180.0)) {
        keep = false;
        break;
      }
    }
    if (keep) filtered.push_back({i, u});
  }
  std::cout << "Filtered to " << filtered.size() << " diverse axes.\n";

  // Octahedron scale:
  double c_cone = 0.025;
  double c_val = 0.00041;
  double delta_val = 0.00024;
  double scale = (c_val + delta_val) / c_cone;
  vec3 p0 = yocto::normalize(u0) * scale;
  double R = 1.75 * (c_val + delta_val);

  vec3 oct[6] = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::cout << "Searching triples for valid cage...\n";
  double best_min_w = -1.0;
  size_t best_i1 = 0, best_i2 = 0, best_i3 = 0;

  for (size_t a = 0; a < filtered.size(); a++) {
    vec3 p1 = yocto::normalize(filtered[a].u);
    for (size_t b = a + 1; b < filtered.size(); b++) {
      vec3 p2 = yocto::normalize(filtered[b].u);
      for (size_t c = b + 1; c < filtered.size(); c++) {
        vec3 p3 = yocto::normalize(filtered[c].u);

        bool all_pos = true;
        double min_w_triple = 1.0;
        for (int k = 0; k < 6; k++) {
          double w[4];
          if (!SolveTetraPoint(p0, p1, p2, p3, oct[k], w)) {
            all_pos = false; break;
          }
          double min_w = std::min({w[0], w[1], w[2], w[3]});
          if (min_w <= 0.0) {
            all_pos = false; break;
          }
          if (min_w < min_w_triple) min_w_triple = min_w;
        }

        if (all_pos && min_w_triple > best_min_w) {
          best_min_w = min_w_triple;
          best_i1 = filtered[a].orig_idx;
          best_i2 = filtered[b].orig_idx;
          best_i3 = filtered[c].orig_idx;
          std::cout << "FOUND STRICTLY POSITIVE CAGE! min_w = " << best_min_w << "\n";
          std::cout << "  indices: " << best_i1 << ", " << best_i2 << ", " << best_i3 << "\n";
          if (best_min_w > 0.005) { // 0.5% margin is plenty!
            goto done;
          }
        }
      }
    }
  }

done:
  if (best_min_w > 0) {
    std::cout << "\nSUCCESS! Winning cage found:\n";
    std::cout << "Axis 0:\n";
    std::cout << "  B = " << ax0.B.ToString() << "\n";
    for (int m = 0; m < 3; m++) {
      std::cout << "  contact " << m << ": v=" << c0[m].vertex << " (" << c0[m].edge_start << "->"
                << c0[m].edge_finish << ", " << c0[m].edge_start2 << "->" << c0[m].edge_finish2
                << ", mix=" << c0[m].mix << ")\n";
    }
    for (size_t idx : {best_i1, best_i2, best_i3}) {
      std::cout << "Axis (base " << idx << "):\n";
      std::cout << "  B = " << base_axes[idx].cert.B.ToString() << "\n";
      for (int m = 0; m < 3; m++) {
        const auto& cm = base_axes[idx].cert.contacts[m];
        std::cout << "  contact " << m << ": v=" << cm.vertex << " (" << cm.edge_start << "->"
                  << cm.edge_finish << ", " << cm.edge_start2 << "->" << cm.edge_finish2
                  << ", mix=" << cm.mix << ")\n";
      }
      std::cout << "  nonzeroWitness: [" << base_axes[idx].cert.nonzero_witness[0] << ", "
                << base_axes[idx].cert.nonzero_witness[1] << ", "
                << base_axes[idx].cert.nonzero_witness[2] << "]\n";
    }
  } else {
    std::cout << "No positive cage found among filtered axes.\n";
  }

  return 0;
}
