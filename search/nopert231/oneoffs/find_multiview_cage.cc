#include <iostream>
#include <vector>
#include <random>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static inline double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static inline bool InTetrahedron(const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3, const vec3 &p, double margin = 1e-6) {
  vec3 d0 = v0 - v3;
  vec3 d1 = v1 - v3;
  vec3 d2 = v2 - v3;
  double d = Det3(d0, d1, d2);
  if (fabs(d) < 1e-12) return false;

  vec3 dp = p - v3;
  double b0 = Det3(dp, d1, d2) / d;
  if (b0 < margin) return false;
  double b1 = Det3(d0, dp, d2) / d;
  if (b1 < margin) return false;
  double b2 = Det3(d0, d1, dp) / d;
  if (b2 < margin) return false;
  double b3 = 1.0 - b0 - b1 - b2;
  return (b3 >= margin);
}

static bool Barycentric4(const BigVecQ3 pts[4], const BigVecQ3 &target, BigRat lam[4]) {
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

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));

  BigRat c_cone("20/10000");   // 0.0020
  BigRat delta("115/100000");  // 0.00115
  BigRat c("140/100000");      // 0.00140

  BigRat v0_scale = (c + delta) / c_cone;
  BigVecQ3 v0 = ctr_ann * v0_scale;
  vec3 v0_f = {v0.x.ToDouble(), v0.y.ToDouble(), v0.z.ToDouble()};

  BigRat target_scale = (c + delta) * BigRat(7, 4);
  double R_f = target_scale.ToDouble();
  vec3 targets_f[6] = {
    {+R_f, 0, 0}, {-R_f, 0, 0},
    {0, +R_f, 0}, {0, -R_f, 0},
    {0, 0, +R_f}, {0, 0, -R_f}
  };

  BigRat z0(0);
  BigVecQ3 targets_exact[6] = {
    BigVecQ3(target_scale, z0, z0),
    BigVecQ3(-target_scale, z0, z0),
    BigVecQ3(z0, target_scale, z0),
    BigVecQ3(z0, -target_scale, z0),
    BigVecQ3(z0, z0, target_scale),
    BigVecQ3(z0, z0, -target_scale)
  };

  // Sample views across sphere
  std::vector<vec3> views;
  for (int x : {-1, 0, 1}) {
    for (int y : {-1, 0, 1}) {
      for (int z : {-1, 0, 1}) {
        if (x == 0 && y == 0 && z == 0) continue;
        views.push_back(yocto::normalize(vec3{(double)x, (double)y, (double)z}));
      }
    }
  }

  std::vector<Tube229::CandidateTriple> all_cands;
  for (const auto &v : views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 6, true);
    for (const auto &cand : cands) all_cands.push_back(cand);
  }

  struct AuditedCand {
    AxisCertificate cert;
    BigVecQ3 center;
    vec3 center_f;
    BigRat delta;
  };
  std::vector<AuditedCand> audited;
  for (const auto &c : all_cands) {
    ContactInfo ct[3] = {c.contacts[0], c.contacts[1], c.contacts[2]};
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat ax_delta;
    std::string fail;
    if (Tube229::AuditAxis(tri, ct, &ax, &center, &ax_delta, &fail, BigRat(0))) {
      if (ax_delta <= delta) {
        audited.push_back({ax, center, {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()}, ax_delta});
      }
    }
  }
  std::cout << "Audited valid axes with delta <= " << delta.ToDouble() << ": " << audited.size() << "\n";

  std::mt19937 rng(42);
  std::uniform_int_distribution<size_t> dist(0, audited.size() - 1);

  for (int iter = 0; iter < 20000000; iter++) {
    size_t i1 = dist(rng), i2 = dist(rng), i3 = dist(rng);
    if (i1 == i2 || i2 == i3 || i1 == i3) continue;

    const vec3 &v1 = audited[i1].center_f;
    const vec3 &v2 = audited[i2].center_f;
    const vec3 &v3 = audited[i3].center_f;

    bool in_double = true;
    for (int k = 0; k < 6; k++) {
      if (!InTetrahedron(v0_f, v1, v2, v3, targets_f[k], 1e-6)) {
        in_double = false; break;
      }
    }
    if (!in_double) continue;

    // Exact check!
    BigVecQ3 pts[4] = {v0, audited[i1].center, audited[i2].center, audited[i3].center};
    bool in_exact = true;
    for (int k = 0; k < 6; k++) {
      BigRat lam[4];
      if (!Barycentric4(pts, targets_exact[k], lam)) { in_exact = false; break; }
      if (lam[0] < 0 || lam[1] < 0 || lam[2] < 0 || lam[3] < 0) { in_exact = false; break; }
    }

    if (in_exact) {
      std::cout << "FOUND COMPLETE WINNING DECOMPOSED CERTIFICATE at iter " << iter << "!\n";
      std::cout << "Indices: " << i1 << ", " << i2 << ", " << i3 << "\n";
      for (int a = 0; a < 3; a++) {
        size_t idx = (a == 0 ? i1 : a == 1 ? i2 : i3);
        const auto &ax = audited[idx];
        std::cout << "// Complement Axis " << (a + 1) << " B=" << ax.cert.B.ToString() << " delta=" << ax.delta.ToString() << "\n";
        for (int c = 0; c < 3; c++) {
          std::cout << "MakeContact(" << ax.cert.contacts[c].edge_start << ", "
                    << ax.cert.contacts[c].edge_finish << ", "
                    << ax.cert.contacts[c].edge_start2 << ", "
                    << ax.cert.contacts[c].edge_finish2 << ", "
                    << ax.cert.contacts[c].mix << ", "
                    << ax.cert.contacts[c].vertex << "),\n";
        }
      }
      return 0;
    }
  }

  std::cout << "Not found in 20M iterations.\n";
  return 1;
}
