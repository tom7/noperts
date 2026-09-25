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
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  vec3 ideal1 = {0.0205096, 0.931624, 0.362843};
  vec3 ideal2 = {-0.82403, -0.551492, 0.129735};
  vec3 ideal3 = {0.865049, -0.461764, -0.196122};

  std::cout << "Collecting audited axes across viewpoints...\n";
  int N = 200;
  std::vector<Tube229::AuditedAxis> all_audited;

  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : cands) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        all_audited.push_back({cert, center, delta});
      }
    }
  }

  std::cout << "Total audited axes: " << all_audited.size() << "\n";

  struct ScoredAxis {
    Tube229::AuditedAxis ax;
    vec3 u;
    double dot;
  };

  std::vector<ScoredAxis> c1, c2, c3;
  for (const auto &ax : all_audited) {
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    double ulen = yocto::length(u);
    if (ulen < 1e-6) continue;
    vec3 unorm = u / ulen;

    c1.push_back({ax, u, yocto::dot(unorm, ideal1)});
    c2.push_back({ax, u, yocto::dot(unorm, ideal2)});
    c3.push_back({ax, u, yocto::dot(unorm, ideal3)});
  }

  std::sort(c1.begin(), c1.end(), [](const ScoredAxis &a, const ScoredAxis &b) { return a.dot > b.dot; });
  std::sort(c2.begin(), c2.end(), [](const ScoredAxis &a, const ScoredAxis &b) { return a.dot > b.dot; });
  std::sort(c3.begin(), c3.end(), [](const ScoredAxis &a, const ScoredAxis &b) { return a.dot > b.dot; });

  // Filter each cluster to unique axes (dot < 0.999)
  auto Deduplicate = [](const std::vector<ScoredAxis> &in, int max_keep) {
    std::vector<ScoredAxis> out;
    for (const auto &s : in) {
      bool dup = false;
      vec3 unorm = s.u / yocto::length(s.u);
      for (const auto &o : out) {
        if (yocto::dot(unorm, o.u / yocto::length(o.u)) > 0.999) {
          dup = true;
          break;
        }
      }
      if (!dup) {
        out.push_back(s);
        if (out.size() >= max_keep) break;
      }
    }
    return out;
  };

  int K = 60;
  auto top1 = Deduplicate(c1, K);
  auto top2 = Deduplicate(c2, K);
  auto top3 = Deduplicate(c3, K);

  std::cout << "Top clusters: c1=" << top1.size() << " (best dot " << top1[0].dot << "), "
            << "c2=" << top2.size() << " (best dot " << top2[0].dot << "), "
            << "c3=" << top3.size() << " (best dot " << top3[0].dot << ")\n";

  double delta = 3.33e-7;
  double box_c = 1e-7;
  double c_cone = 0.028;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct_dirs = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  double best_min_l = -1e9;
  int bi = -1, bj = -1, bk = -1;

  for (size_t i = 0; i < top1.size(); i++) {
    vec3 d1 = top1[i].u - v0;
    for (size_t j = 0; j < top2.size(); j++) {
      vec3 d2 = top2[j].u - v0;
      vec3 c12 = yocto::cross(d1, d2);
      if (yocto::length(c12) < 1e-6) continue;

      for (size_t k = 0; k < top3.size(); k++) {
        vec3 d3 = top3[k].u - v0;
        double det = yocto::dot(c12, d3);
        if (std::abs(det) < 1e-8) continue;

        vec3 c23 = yocto::cross(d2, d3);
        vec3 c31 = yocto::cross(d3, d1);

        double min_l = 1e9;
        for (int m = 0; m < 6; m++) {
          vec3 dp = oct_dirs[m] * R - v0;
          double l1 = yocto::dot(dp, c23) / det;
          double l2 = yocto::dot(dp, c31) / det;
          double l3 = yocto::dot(dp, c12) / det;
          double l0 = 1.0 - l1 - l2 - l3;
          double min_vert = std::min({l0, l1, l2, l3});
          if (min_vert < min_l) min_l = min_vert;
          if (min_l <= best_min_l) break;
        }

        if (min_l > best_min_l) {
          best_min_l = min_l;
          bi = i; bj = j; bk = k;
          std::cout << "New best min_l: " << best_min_l << " with ("
                    << bi << ", " << bj << ", " << bk << ")\n";
          if (best_min_l > 0) {
            std::cout << "SUCCESS! Strictly positive cage found!\n";
            std::cout << "Axis 1 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  v=" << top1[bi].ax.cert.contacts[c].vertex
                        << " mix=" << top1[bi].ax.cert.contacts[c].mix
                        << " e1=" << top1[bi].ax.cert.contacts[c].edge_start << "->" << top1[bi].ax.cert.contacts[c].edge_finish
                        << " e2=" << top1[bi].ax.cert.contacts[c].edge_start2 << "->" << top1[bi].ax.cert.contacts[c].edge_finish2 << "\n";
            }
            std::cout << "Axis 2 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  v=" << top2[bj].ax.cert.contacts[c].vertex
                        << " mix=" << top2[bj].ax.cert.contacts[c].mix
                        << " e1=" << top2[bj].ax.cert.contacts[c].edge_start << "->" << top2[bj].ax.cert.contacts[c].edge_finish
                        << " e2=" << top2[bj].ax.cert.contacts[c].edge_start2 << "->" << top2[bj].ax.cert.contacts[c].edge_finish2 << "\n";
            }
            std::cout << "Axis 3 contacts:\n";
            for (int c = 0; c < 3; c++) {
              std::cout << "  v=" << top3[bk].ax.cert.contacts[c].vertex
                        << " mix=" << top3[bk].ax.cert.contacts[c].mix
                        << " e1=" << top3[bk].ax.cert.contacts[c].edge_start << "->" << top3[bk].ax.cert.contacts[c].edge_finish
                        << " e2=" << top3[bk].ax.cert.contacts[c].edge_start2 << "->" << top3[bk].ax.cert.contacts[c].edge_finish2 << "\n";
            }
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Overall best min_l: " << best_min_l << "\n";
  return 0;
}
