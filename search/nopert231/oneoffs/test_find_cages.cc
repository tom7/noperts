#include <iostream>
#include <string>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static bool Bary4(const BigVecQ3 pts[4], const BigVecQ3 &target, BigRat lam[4]) {
  BigVecQ3 v0 = pts[0] - pts[3];
  BigVecQ3 v1 = pts[1] - pts[3];
  BigVecQ3 v2 = pts[2] - pts[3];
  BigVecQ3 w = target - pts[3];
  BigRat den = BigVecQ3::Det(v0, v1, v2);
  if (den == 0) return false;
  lam[0] = BigVecQ3::Det(w, v1, v2) / den;
  lam[1] = BigVecQ3::Det(v0, w, v2) / den;
  lam[2] = BigVecQ3::Det(v0, v1, w) / den;
  lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
  return true;
}

int main() {
  // Candidate annular axis 0 (contacts 2, 4, 14)
  ContactInfo a0_contacts[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  // Test problematic cells from depth 9 and 10:
  std::vector<std::string> paths = {
    "031213020", "031213021", "031213022", "031213023",
    "031213031", "031213032", "031213033",
    "03121303021", "03121303022", "03121303023"
  };

  for (const std::string &path : paths) {
    TriangleQ tri = TriangleFromPath(path);
    std::cout << "\nTesting cell " << path << ":\n";

    // 1. Audit Axis 0
    AxisCertificate ax0;
    BigVecQ3 center0;
    BigRat delta0;
    std::string err;
    if (!Tube229::AuditAxis(tri, a0_contacts, &ax0, &center0, &delta0, &err, BigRat(5, 1000))) {
      std::cout << "  Axis 0 audit failed: " << err << "\n";
      continue;
    }
    std::cout << "  Axis 0 center: (" << center0.x.ToDouble() << ", "
              << center0.y.ToDouble() << ", " << center0.z.ToDouble() << ")\n";

    // 2. Find all hull support axes with zero defect
    std::vector<Tube229::AuditedAxis> zero_axes = Tube229::FindAllHullSupportAxes(tri, 200);
    std::cout << "  Found " << zero_axes.size() << " zero-defect hull axes\n";

    double norm0 = std::sqrt((center0.x * center0.x + center0.y * center0.y + center0.z * center0.z).ToDouble());
    double max_cos = -2.0;
    int best_cos_idx = -1;
    for (size_t a = 0; a < zero_axes.size(); a++) {
      double norm_a = std::sqrt((zero_axes[a].center.x * zero_axes[a].center.x +
                                 zero_axes[a].center.y * zero_axes[a].center.y +
                                 zero_axes[a].center.z * zero_axes[a].center.z).ToDouble());
      double dot = (BigVecQ3::Dot(center0, zero_axes[a].center)).ToDouble();
      double cos_val = dot / (norm0 * norm_a);
      if (cos_val > max_cos) {
        max_cos = cos_val;
        best_cos_idx = a;
      }
    }
    std::cout << "  Best normalized alignment with center0: idx=" << best_cos_idx
              << " cos=" << max_cos << " (angle=" << (std::acos(std::max(-1.0, std::min(1.0, max_cos))) * 180.0 / 3.14159265) << " deg)\n";
    if (best_cos_idx >= 0) {
      std::cout << "    Contacts: (" << zero_axes[best_cos_idx].cert.contacts[0].vertex << ", "
                << zero_axes[best_cos_idx].cert.contacts[1].vertex << ", "
                << zero_axes[best_cos_idx].cert.contacts[2].vertex << ")\n";
    }

    // Check if any 4 zero-defect axes cage the origin directly!
    bool found_zero_cage = false;
    for (size_t i0 = 0; i0 < std::min((size_t)30, zero_axes.size()) && !found_zero_cage; i0++) {
      for (size_t i1 = i0 + 1; i1 < std::min((size_t)30, zero_axes.size()) && !found_zero_cage; i1++) {
        for (size_t i2 = i1 + 1; i2 < std::min((size_t)30, zero_axes.size()) && !found_zero_cage; i2++) {
          for (size_t i3 = i2 + 1; i3 < std::min((size_t)30, zero_axes.size()) && !found_zero_cage; i3++) {
            BigVecQ3 pts[4] = {
              zero_axes[i0].center,
              zero_axes[i1].center,
              zero_axes[i2].center,
              zero_axes[i3].center
            };
            BigRat lam[4];
            BigVecQ3 origin(BigRat(0), BigRat(0), BigRat(0));
            if (Bary4(pts, origin, lam) && lam[0] > 0 && lam[1] > 0 && lam[2] > 0 && lam[3] > 0) {
              BigRat r_cage = Tube229::ExactTetrahedronAxisRadius(pts);
              BigRat max_d = zero_axes[i0].delta;
              if (zero_axes[i1].delta > max_d) max_d = zero_axes[i1].delta;
              if (zero_axes[i2].delta > max_d) max_d = zero_axes[i2].delta;
              if (zero_axes[i3].delta > max_d) max_d = zero_axes[i3].delta;
              if (r_cage > max_d) {
                std::cout << "  FOUND 4 ZERO-DEFECT AXES CAGING ORIGIN! indices=("
                          << i0 << ", " << i1 << ", " << i2 << ", " << i3 << ")\n";
                std::cout << "    r_cage=" << r_cage.ToDouble() << " max_d=" << max_d.ToDouble()
                          << " margin=" << (r_cage - max_d).ToDouble() << "\n";
                found_zero_cage = true;
                break;
              }
            }
          }
        }
      }
    }
    if (!found_zero_cage) {
      std::cout << "  No 4 zero-defect axes caged the origin among first 30.\n";
    }

    // 3. Search for a triplet of zero-defect axes that cages with Axis 0
    bool found_cage = false;
    for (size_t i = 0; i < zero_axes.size() && !found_cage; i++) {
      for (size_t j = i + 1; j < zero_axes.size() && !found_cage; j++) {
        for (size_t k = j + 1; k < zero_axes.size() && !found_cage; k++) {
          BigVecQ3 centers[4] = {center0, zero_axes[i].center, zero_axes[j].center, zero_axes[k].center};
          BigRat lam[4];
          if (Bary4(centers, BigVecQ3(BigRat(0), BigRat(0), BigRat(0)), lam)) {
            if (lam[0] > 0 && lam[1] > 0 && lam[2] > 0 && lam[3] > 0) {
              BigRat r_cage = Tube229::ExactTetrahedronAxisRadius(centers);
              BigRat max_delta = delta0;
              if (zero_axes[i].delta > max_delta) max_delta = zero_axes[i].delta;
              if (zero_axes[j].delta > max_delta) max_delta = zero_axes[j].delta;
              if (zero_axes[k].delta > max_delta) max_delta = zero_axes[k].delta;
              BigRat c_eff = r_cage - max_delta;
              if (c_eff > 0) {
                std::cout << "  FOUND CAGING TET! indices=(" << i << ", " << j << ", " << k << ")\n"
                          << "    lambda=[" << lam[0].ToDouble() << ", " << lam[1].ToDouble()
                          << ", " << lam[2].ToDouble() << ", " << lam[3].ToDouble() << "]\n"
                          << "    r_cage=" << r_cage.ToDouble() << " max_delta=" << max_delta.ToDouble()
                          << " c_eff=" << c_eff.ToDouble() << "\n";

                // Check Inner Core Axis
                AxisCertificate inner_core;
                BigVecQ3 inner_center;
                BigRat inner_delta;
                std::string inner_fail;
                if (!Tube229::FindHullSupportAxis(tri, &inner_core, &inner_center, &inner_delta, &inner_fail)) {
                  std::cout << "    FindHullSupportAxis failed: " << inner_fail << "\n";
                } else {
                  std::cout << "    Inner core axis found: delta=" << inner_delta.ToDouble()
                            << " B=" << inner_core.B.ToDouble() << "\n";
                  BigRat mu = BigVecQ3::Dot(center0, inner_center);
                  std::cout << "    Dot(center0, inner_center) = " << mu.ToDouble() << "\n";

                  // Test parameters r, r_min, c_cone
                  BigVecQ3 edges[3] = {
                    Tube229::GetExactEdge(a0_contacts[0]),
                    Tube229::GetExactEdge(a0_contacts[1]),
                    Tube229::GetExactEdge(a0_contacts[2])
                  };
                  BigVecQ3 w_coeffs[3] = {
                    BigVecQ3::Cross(edges[1], edges[2]),
                    BigVecQ3::Cross(edges[2], edges[0]),
                    BigVecQ3::Cross(edges[0], edges[1])
                  };
                  BigRat w_upper[3];
                  for (int m = 0; m < 3; m++) {
                    BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
                    for (int c = 1; c < 3; c++) {
                      BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
                      if (val > w_max) w_max = val;
                    }
                    w_upper[m] = w_max;
                  }
                  BigRat D0(0);
                  for (int m = 0; m < 3; m++) {
                    int sel = a0_contacts[m].vertex;
                    BigVecQ3 v_sel = Tube229::VertexQ(sel);
                    BigRat max_m_defect(0);
                    for (int k = 0; k < 20; k++) {
                      if (k == sel) continue;
                      BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
                      BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta_v);
                      BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
                      for (int c = 1; c < 3; c++) {
                        BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
                        if (val > max_s) max_s = val;
                      }
                      if (max_s > max_m_defect) max_m_defect = max_s;
                    }
                    D0 = D0 + max_m_defect * w_upper[m];
                  }
                  std::cout << "    Defect D0 = " << D0.ToDouble() << "\n";

                  // Test parameters r, r_min, c_cone
                  BigRat c_cone = r_cage;
                  BigRat c_margin = c_cone - max_delta;
                  std::cout << "    c_margin = " << c_margin.ToDouble() << "\n";

                  // Try r_min = 1/5000, 1/10000, 1/20000
                  for (int r_min_denom : {1000, 2000, 5000, 10000, 20000}) {
                    for (int r_denom : {100, 200, 500, 1000, 2000}) {
                      if (r_min_denom <= r_denom) continue;
                      BigRat r_min(1, r_min_denom);
                      BigRat r(1, r_denom);
                      // Annular dominance check:
                      // ((1/2) r^2 B0 + D0)^2 <= r_min^2 (1 - (1/4) r^2) * (c_cone - delta0)^2 B0^2
                      BigRat lhs = (BigRat(1, 2) * r * r * ax0.B + D0);
                      lhs = lhs * lhs;
                      BigRat rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (c_margin * c_margin * ax0.B * ax0.B);
                      if (lhs <= rhs) {
                        std::cout << "    ANNULAR DOMINANCE HOLDS! r_min=1/" << r_min_denom
                                  << ", r=1/" << r_denom << " (ratio lhs/rhs = "
                                  << (lhs / rhs).ToDouble() << ")\n";
                      }
                    }
                  }
                }
                found_cage = true;
              }
            }
          }
        }
      }
    }
    if (!found_cage) {
      std::cout << "  No caging tet found among zero-defect axes.\n";
    }
  }

  return 0;
}
