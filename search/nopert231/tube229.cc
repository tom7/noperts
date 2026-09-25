#include "tube229.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <format>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "base/stringprintf.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "nopert229.h"
#include "tubetree229.h"
#include "util.h"
#include "yocto-math.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

static inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

BigVecQ3 Tube229::VertexQ(int v) {
  const auto &vs = GetVerticesQ();
  return BigVecQ3(vs[v][0], vs[v][1], vs[v][2]);
}

vec3 Tube229::GetDoubleEdge(const ContactInfo &c) {
  vec3 v_start = Vertex(c.edge_start);
  vec3 v_finish = Vertex(c.edge_finish);
  vec3 v_start2 = Vertex(c.edge_start2);
  vec3 v_finish2 = Vertex(c.edge_finish2);
  double mixD = c.mix / 1000.0;
  return (v_start - v_finish) * mixD + (v_start2 - v_finish2) * (1.0 - mixD);
}

BigVecQ3 Tube229::GetExactEdge(const ContactInfo &c) {
  const auto &vs = GetVerticesQ();
  BigVecQ3 v_start(vs[c.edge_start][0], vs[c.edge_start][1], vs[c.edge_start][2]);
  BigVecQ3 v_finish(vs[c.edge_finish][0], vs[c.edge_finish][1], vs[c.edge_finish][2]);
  BigVecQ3 v_start2(vs[c.edge_start2][0], vs[c.edge_start2][1], vs[c.edge_start2][2]);
  BigVecQ3 v_finish2(vs[c.edge_finish2][0], vs[c.edge_finish2][1], vs[c.edge_finish2][2]);
  BigRat mixQ(c.mix, 1000);
  return (v_start - v_finish) * mixQ + (v_start2 - v_finish2) * (BigRat(1) - mixQ);
}

static inline double Cross2(const vec2 &a, const vec2 &b) {
  return a.x * b.y - a.y * b.x;
}

std::vector<int> Tube229::ConvexHull2D(const std::vector<vec2> &points) {
  int n = points.size();
  std::vector<int> p(n);
  std::iota(p.begin(), p.end(), 0);
  std::sort(p.begin(), p.end(), [&](int a, int b) {
    if (points[a].x != points[b].x) return points[a].x < points[b].x;
    return points[a].y < points[b].y;
  });

  auto half = [&](const std::vector<int> &indices) {
    std::vector<int> ans;
    for (int idx : indices) {
      while (ans.size() >= 2) {
        vec2 a = points[ans[ans.size() - 2]];
        vec2 b = points[ans[ans.size() - 1]];
        vec2 pt = points[idx];
        vec2 ab = b - a;
        vec2 bp = pt - b;
        if (Cross2(ab, bp) > 1e-14) break;
        ans.pop_back();
      }
      ans.push_back(idx);
    }
    return ans;
  };

  std::vector<int> lower = half(p);
  std::vector<int> rev_p = p;
  std::reverse(rev_p.begin(), rev_p.end());
  std::vector<int> upper = half(rev_p);

  std::vector<int> hull;
  if (!lower.empty()) lower.pop_back();
  if (!upper.empty()) upper.pop_back();
  hull.insert(hull.end(), lower.begin(), lower.end());
  hull.insert(hull.end(), upper.begin(), upper.end());
  return hull;
}

std::vector<ContactInfo> Tube229::GenerateSilhouetteContacts(
    const vec3 &view,
    const std::vector<int> &mix_samples_permille) {
  std::vector<ContactInfo> contacts;
  double vlen = yocto::length(view);
  if (vlen < 1e-12) return contacts;
  vec3 unit_view = view / vlen;

  int axis_index = 0;
  double min_abs = 1e30;
  for (int i = 0; i < 3; i++) {
    if (std::abs(unit_view[i]) < min_abs) {
      min_abs = std::abs(unit_view[i]);
      axis_index = i;
    }
  }
  vec3 axis = (axis_index == 0 ? vec3{1, 0, 0} : (axis_index == 1 ? vec3{0, 1, 0} : vec3{0, 0, 1}));
  vec3 first = yocto::normalize(yocto::cross(unit_view, axis));
  vec3 second = yocto::cross(unit_view, first);

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> cycle = ConvexHull2D(projected);
  int H = cycle.size();

  for (int pos = 0; pos < H; pos++) {
    int v = cycle[pos];
    int prev = cycle[(pos - 1 + H) % H];
    int next = cycle[(pos + 1) % H];

    for (int mix : mix_samples_permille) {
      ContactInfo ci;
      ci.vertex = v;
      ci.edge_start = prev;
      ci.edge_finish = v;
      ci.edge_start2 = v;
      ci.edge_finish2 = next;
      ci.mix = mix;
      contacts.push_back(ci);
    }
  }
  return contacts;
}

std::vector<Tube229::CandidateTriple> Tube229::GenerateCandidateTriples(
    const TriangleQ &tri,
    const std::vector<ContactInfo> &contacts,
    double screen_support_error) {
  std::vector<CandidateTriple> out_candidates;
  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  double vlen = yocto::length(centroid);
  if (vlen < 1e-12) return out_candidates;
  vec3 unit_view = centroid / vlen;

  struct ValidContact {
    ContactInfo ci;
    vec3 edge;
    vec3 lift;
    vec3 tau;
    double strict_slack;
  };

  std::vector<ValidContact> valid;
  for (const auto &c : contacts) {
    vec3 edge = GetDoubleEdge(c);
    int sel = c.vertex;
    bool ok = true;
    double strict_slack = 1e30;

    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta = Vertex(k) - Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta);
      double u0 = yocto::dot(tri_f[0], coeff);
      double u1 = yocto::dot(tri_f[1], coeff);
      double u2 = yocto::dot(tri_f[2], coeff);
      double max_u = std::max({u0, u1, u2});
      strict_slack = std::min(strict_slack, -max_u);
      if (max_u > screen_support_error) { ok = false; break; }
    }
    if (ok) {
      vec3 lift = yocto::cross(centroid, edge);
      vec3 tau = yocto::cross(Vertex(sel), lift);
      valid.push_back({c, edge, lift, tau, strict_slack});
    }
  }

  int V = valid.size();
  if (V < 3) return out_candidates;
  out_candidates.reserve(V * 100);

  // Precompute pair quantities across valid contacts
  struct PairInfo {
    double lift_dot;      // dot(unit_view, cross(lift_a, lift_b))
    double dot_tri0;      // dot(tri_f[0], cross(edge_a, edge_b))
    double dot_cen;       // dot(centroid, cross(edge_a, edge_b))
    double min_w;         // min over corners of dot(tri_f[c], cross(edge_a, edge_b))
    double max_w;         // max over corners of dot(tri_f[c], cross(edge_a, edge_b))
  };

  std::vector<PairInfo> pair_table(V * V);
  for (int a = 0; a < V; a++) {
    for (int b = a + 1; b < V; b++) {
      vec3 c_lift = yocto::cross(valid[a].lift, valid[b].lift);
      double l_dot = yocto::dot(unit_view, c_lift);

      vec3 c_edge = yocto::cross(valid[a].edge, valid[b].edge);
      double d0 = yocto::dot(tri_f[0], c_edge);
      double d1 = yocto::dot(tri_f[1], c_edge);
      double d2 = yocto::dot(tri_f[2], c_edge);
      double d_cen = yocto::dot(centroid, c_edge);

      double min_d = std::min({d0, d1, d2});
      double max_d = std::max({d0, d1, d2});

      pair_table[a * V + b] = {l_dot, d0, d_cen, min_d, max_d};
      pair_table[b * V + a] = {-l_dot, -d0, -d_cen, -max_d, -min_d};
    }
  }

  for (int i = 0; i < V; i++) {
    const auto &vi = valid[i];
    const PairInfo *row_i = &pair_table[i * V];

    for (int j = i + 1; j < V; j++) {
      const auto &vj = valid[j];
      const PairInfo &p_ij = row_i[j];
      const PairInfo *row_j = &pair_table[j * V];

      for (int k = j + 1; k < V; k++) {
        const auto &vk = valid[k];
        const PairInfo &p_jk = row_j[k];
        const PairInfo &p_ik = row_i[k];

        double w0 = p_jk.lift_dot;
        double w1 = -p_ik.lift_dot;
        double w2 = p_ij.lift_dot;

        if (w0 <= 1e-12 && w1 <= 1e-12 && w2 <= 1e-12) {
          w0 = -w0; w1 = -w1; w2 = -w2;
        }
        if (w0 < -1e-10 || w1 < -1e-10 || w2 < -1e-10) continue;

        double probe0 = p_jk.dot_tri0;
        double probe1 = -p_ik.dot_tri0;
        double probe2 = p_ij.dot_tri0;

        bool swap_12 = (std::max({probe0, probe1, probe2}) < 0);

        double w_min[3], w_max[3], cen_w[3];
        ContactInfo sel_contacts[3];
        double sel_slack[3];
        const vec3 *term[3];

        if (!swap_12) {
          w_min[0] = p_jk.min_w + screen_support_error;
          if (w_min[0] < 0) continue;
          w_max[0] = p_jk.max_w + screen_support_error;
          cen_w[0] = p_jk.dot_cen;

          w_min[1] = -p_ik.max_w + screen_support_error;
          if (w_min[1] < 0) continue;
          w_max[1] = -p_ik.min_w + screen_support_error;
          cen_w[1] = -p_ik.dot_cen;

          w_min[2] = p_ij.min_w + screen_support_error;
          if (w_min[2] < 0) continue;
          w_max[2] = p_ij.max_w + screen_support_error;
          cen_w[2] = p_ij.dot_cen;

          sel_contacts[0] = vi.ci;
          sel_contacts[1] = vj.ci;
          sel_contacts[2] = vk.ci;

          sel_slack[0] = vi.strict_slack;
          sel_slack[1] = vj.strict_slack;
          sel_slack[2] = vk.strict_slack;

          term[0] = &vi.tau;
          term[1] = &vj.tau;
          term[2] = &vk.tau;
        } else {
          w_min[0] = -p_jk.max_w + screen_support_error;
          if (w_min[0] < 0) continue;
          w_max[0] = -p_jk.min_w + screen_support_error;
          cen_w[0] = -p_jk.dot_cen;

          w_min[1] = -p_ij.max_w + screen_support_error;
          if (w_min[1] < 0) continue;
          w_max[1] = -p_ij.min_w + screen_support_error;
          cen_w[1] = -p_ij.dot_cen;

          w_min[2] = p_ik.min_w + screen_support_error;
          if (w_min[2] < 0) continue;
          w_max[2] = p_ik.max_w + screen_support_error;
          cen_w[2] = p_ik.dot_cen;

          sel_contacts[0] = vi.ci;
          sel_contacts[1] = vk.ci;
          sel_contacts[2] = vj.ci;

          sel_slack[0] = vi.strict_slack;
          sel_slack[1] = vk.strict_slack;
          sel_slack[2] = vj.strict_slack;

          term[0] = &vi.tau;
          term[1] = &vk.tau;
          term[2] = &vj.tau;
        }

        double max_weight_lower = std::max({w_min[0], w_min[1], w_min[2]});
        if (max_weight_lower <= 0) continue;

        double B = 2.0 * (w_max[0] + w_max[1] + w_max[2]);
        if (B <= 1e-12) continue;

        double strict_slack = std::min({sel_slack[0], sel_slack[1], sel_slack[2]});

        vec3 variation = (*term[0]) * cen_w[0] + (*term[1]) * cen_w[1] + (*term[2]) * cen_w[2];
        vec3 normalized_a = variation / B;

        CandidateTriple cand;
        cand.contacts[0] = sel_contacts[0];
        cand.contacts[1] = sel_contacts[1];
        cand.contacts[2] = sel_contacts[2];
        cand.normalized_a = normalized_a;
        cand.B = B;
        cand.strict_slack = strict_slack;
        out_candidates.push_back(cand);
      }
    }
  }
  return out_candidates;
}

bool Tube229::DoubleCheckAxis(
    const TriangleQ &tri,
    const ContactInfo contacts[3],
    CandidateTriple *out_cand,
    double screen_support_error) {

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  double vlen = yocto::length(centroid);
  if (vlen < 1e-12) return false;

  vec3 c_edges[3];
  ContactInfo sel_contacts[3];
  int sel_indices[3];
  double sel_slack[3];

  for (int m = 0; m < 3; m++) {
    const auto &c = contacts[m];
    vec3 edge = GetDoubleEdge(c);
    int sel = c.vertex;
    double strict_slack = 1e30;

    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta = Vertex(k) - Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta);
      double u0 = yocto::dot(tri_f[0], coeff);
      double u1 = yocto::dot(tri_f[1], coeff);
      double u2 = yocto::dot(tri_f[2], coeff);
      double max_u = std::max({u0, u1, u2});
      strict_slack = std::min(strict_slack, -max_u);
      if (max_u > screen_support_error) return false;
    }
    c_edges[m] = edge;
    sel_contacts[m] = c;
    sel_indices[m] = sel;
    sel_slack[m] = strict_slack;
  }

  vec3 probe = {yocto::dot(tri_f[0], yocto::cross(c_edges[1], c_edges[2])),
                yocto::dot(tri_f[0], yocto::cross(c_edges[2], c_edges[0])),
                yocto::dot(tri_f[0], yocto::cross(c_edges[0], c_edges[1]))};
  if (std::max({probe[0], probe[1], probe[2]}) < 0) {
    std::swap(sel_contacts[1], sel_contacts[2]);
    std::swap(c_edges[1], c_edges[2]);
    std::swap(sel_indices[1], sel_indices[2]);
    std::swap(sel_slack[1], sel_slack[2]);
  }

  vec3 weight_coeffs[3] = {
    yocto::cross(c_edges[1], c_edges[2]),
    yocto::cross(c_edges[2], c_edges[0]),
    yocto::cross(c_edges[0], c_edges[1])
  };

  double max_weight_lower = -1e30;
  double weights_at_max[3] = {0, 0, 0};
  for (int m = 0; m < 3; m++) {
    double w0 = yocto::dot(tri_f[0], weight_coeffs[m]);
    double w1 = yocto::dot(tri_f[1], weight_coeffs[m]);
    double w2 = yocto::dot(tri_f[2], weight_coeffs[m]);
    double w_min = std::min({w0, w1, w2}) + screen_support_error;
    double w_max = std::max({w0, w1, w2}) + screen_support_error;
    if (w_min < 0) return false;
    max_weight_lower = std::max(max_weight_lower, w_min);
    weights_at_max[m] = w_max;
  }
  if (max_weight_lower <= 0) return false;

  double strict_slack = std::min({sel_slack[0], sel_slack[1], sel_slack[2]});
  vec3 weights = {yocto::dot(centroid, weight_coeffs[0]),
                  yocto::dot(centroid, weight_coeffs[1]),
                  yocto::dot(centroid, weight_coeffs[2])};
  double B = 2.0 * (weights_at_max[0] + weights_at_max[1] + weights_at_max[2]);
  if (B <= 1e-12) return false;

  vec3 variation = {0, 0, 0};
  for (int m = 0; m < 3; m++) {
    vec3 lift = yocto::cross(centroid, c_edges[m]);
    vec3 term = yocto::cross(Vertex(sel_indices[m]), lift);
    variation = variation + term * weights[m];
  }
  vec3 normalized_a = variation / B;

  if (out_cand) {
    out_cand->contacts[0] = sel_contacts[0];
    out_cand->contacts[1] = sel_contacts[1];
    out_cand->contacts[2] = sel_contacts[2];
    out_cand->normalized_a = normalized_a;
    out_cand->B = B;
    out_cand->strict_slack = strict_slack;
  }
  return true;
}

std::vector<Tube229::CandidateTriple> Tube229::GenerateCandidatesForView(
    const vec3 &view,
    const TriangleQ &tri,
    bool evaluate_over_triangle,
    int cone_samples,
    bool include_boundaries,
    double screen_support_error) {

  std::vector<CandidateTriple> out_candidates;
  double vlen = yocto::length(view);
  if (vlen < 1e-12) return out_candidates;
  vec3 unit_view = view / vlen;

  int axis_index = 0;
  double min_abs = 1e30;
  for (int i = 0; i < 3; i++) {
    if (std::abs(unit_view[i]) < min_abs) {
      min_abs = std::abs(unit_view[i]);
      axis_index = i;
    }
  }
  vec3 axis = (axis_index == 0 ? vec3{1, 0, 0} : (axis_index == 1 ? vec3{0, 1, 0} : vec3{0, 0, 1}));
  vec3 first = yocto::cross(unit_view, axis);
  double first_len = yocto::length(first);
  if (first_len < 1e-12) return out_candidates;
  first = first / first_len;
  vec3 second = yocto::cross(unit_view, first);

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{
      yocto::dot(Vertex(k), first),
      yocto::dot(Vertex(k), second),
    };
  }
  std::vector<int> cycle = ConvexHull2D(projected);
  int H = cycle.size();
  if (H < 3) return out_candidates;

  std::vector<ContactInfo> contacts;
  std::vector<vec3> lifts;
  for (int pos = 0; pos < H; pos++) {
    int vertex = cycle[pos];
    int previous = cycle[(pos - 1 + H) % H];
    int following = cycle[(pos + 1) % H];

    std::vector<double> samples;
    for (int s = 0; s < cone_samples; s++) {
      samples.push_back((s + 1.0) / (cone_samples + 1.0));
    }
    if (include_boundaries) {
      samples.push_back(0.0);
      samples.push_back(0.001);
      samples.push_back(0.999);
      samples.push_back(1.0);
      std::sort(samples.begin(), samples.end());
      samples.erase(std::unique(samples.begin(), samples.end()), samples.end());
    }

    for (double lam : samples) {
      int mix = std::clamp(static_cast<int>(std::round(1000.0 * lam)), 0, 1000);
      ContactInfo ci;
      ci.vertex = vertex;
      ci.edge_start = previous;
      ci.edge_finish = vertex;
      ci.edge_start2 = vertex;
      ci.edge_finish2 = following;
      ci.mix = mix;
      vec3 edge = GetDoubleEdge(ci);
      vec3 lift = yocto::cross(unit_view, edge);
      contacts.push_back(ci);
      lifts.push_back(lift);
    }
  }

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  struct ContactSupportData {
    vec3 edge;
    int selected;
    double strict_slack;
    bool support_ok;
  };

  std::vector<ContactSupportData> supp_cache(contacts.size());
  for (size_t i = 0; i < contacts.size(); i++) {
    const auto &c = contacts[i];
    vec3 edge = GetDoubleEdge(c);
    int sel = c.vertex;
    double strict_slack = 1e30;
    bool ok = true;
    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta = Vertex(k) - Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta);
      double upper = evaluate_over_triangle
          ? std::max({yocto::dot(tri_f[0], coeff), yocto::dot(tri_f[1], coeff), yocto::dot(tri_f[2], coeff)}) + screen_support_error
          : yocto::dot(centroid, coeff) + screen_support_error;
      strict_slack = std::min(strict_slack, -upper);
      if (upper > 0) {
        ok = false;
        break;
      }
    }
    supp_cache[i] = {edge, sel, strict_slack, ok};
  }

  std::vector<int> valid_idx;
  for (size_t i = 0; i < contacts.size(); i++) {
    if (supp_cache[i].support_ok) valid_idx.push_back(i);
  }

  int V = valid_idx.size();
  for (int ii = 0; ii < V; ii++) {
    int i = valid_idx[ii];
    for (int jj = ii + 1; jj < V; jj++) {
      int j = valid_idx[jj];
      for (int kk = jj + 1; kk < V; kk++) {
        int k = valid_idx[kk];

        vec3 lifts_triple[3] = {lifts[i], lifts[j], lifts[k]};
        vec3 w = {yocto::dot(unit_view, yocto::cross(lifts_triple[1], lifts_triple[2])),
                  yocto::dot(unit_view, yocto::cross(lifts_triple[2], lifts_triple[0])),
                  yocto::dot(unit_view, yocto::cross(lifts_triple[0], lifts_triple[1]))};
        if (w[0] <= 1e-12 && w[1] <= 1e-12 && w[2] <= 1e-12) {
          w = -w;
        }
        if (w[0] < -1e-10 || w[1] < -1e-10 || w[2] < -1e-10) continue;

        ContactInfo sel_contacts[3] = {contacts[i], contacts[j], contacts[k]};
        vec3 c_edges[3] = {supp_cache[i].edge, supp_cache[j].edge, supp_cache[k].edge};
        ContactSupportData c_supp[3] = {supp_cache[i], supp_cache[j], supp_cache[k]};

        vec3 probe = {yocto::dot(tri_f[0], yocto::cross(c_edges[1], c_edges[2])),
                      yocto::dot(tri_f[0], yocto::cross(c_edges[2], c_edges[0])),
                      yocto::dot(tri_f[0], yocto::cross(c_edges[0], c_edges[1]))};
        if (std::max({probe[0], probe[1], probe[2]}) < 0) {
          std::swap(sel_contacts[1], sel_contacts[2]);
          std::swap(c_edges[1], c_edges[2]);
          std::swap(c_supp[1], c_supp[2]);
        }

        vec3 weight_coeffs[3] = {
          yocto::cross(c_edges[1], c_edges[2]),
          yocto::cross(c_edges[2], c_edges[0]),
          yocto::cross(c_edges[0], c_edges[1])
        };

        bool weight_ok = true;
        double max_weight_lower = -1e30;
        double weights_at_max[3] = {0, 0, 0};
        for (int m = 0; m < 3; m++) {
          double w0 = yocto::dot(tri_f[0], weight_coeffs[m]);
          double w1 = yocto::dot(tri_f[1], weight_coeffs[m]);
          double w2 = yocto::dot(tri_f[2], weight_coeffs[m]);
          double w_min = std::min({w0, w1, w2}) - screen_support_error;
          double w_max = std::max({w0, w1, w2}) + screen_support_error;
          if (w_min < 0) { weight_ok = false; break; }
          max_weight_lower = std::max(max_weight_lower, w_min);
          weights_at_max[m] = w_max;
        }
        if (!weight_ok || max_weight_lower <= 0) continue;

        double strict_slack = std::min({c_supp[0].strict_slack, c_supp[1].strict_slack, c_supp[2].strict_slack});

        vec3 weights = {yocto::dot(centroid, weight_coeffs[0]),
                        yocto::dot(centroid, weight_coeffs[1]),
                        yocto::dot(centroid, weight_coeffs[2])};
        double B = 2.0 * (weights_at_max[0] + weights_at_max[1] + weights_at_max[2]);
        vec3 variation = {0, 0, 0};
        for (int m = 0; m < 3; m++) {
          vec3 lift = yocto::cross(centroid, c_edges[m]);
          vec3 term = yocto::cross(Vertex(c_supp[m].selected), lift);
          variation = variation + term * weights[m];
        }
        vec3 normalized_a = variation / B;

        CandidateTriple cand;
        cand.contacts[0] = sel_contacts[0];
        cand.contacts[1] = sel_contacts[1];
        cand.contacts[2] = sel_contacts[2];
        cand.normalized_a = normalized_a;
        cand.strict_slack = strict_slack;
        cand.B = B;
        out_candidates.push_back(cand);
      }
    }
  }

  return out_candidates;
}

std::vector<Tube229::CandidateTriple> Tube229::FindOpposingCandidates(
    const TriangleQ &tri,
    const vec3 &oppose_dir,
    int max_candidates,
    double screen_support_error) {
  double nlen = yocto::length(oppose_dir);
  if (nlen < 1e-12) return {};
  vec3 unit_n = oppose_dir / nlen;

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  // Multi-view sampling: centroid and the three triangle corners
  std::vector<vec3> sample_views = {centroid, tri_f[0], tri_f[1], tri_f[2]};

  // Fine mix permille grid to capture support edges and transition features
  std::vector<int> fine_mixes = {
      0, 1, 10, 50, 100, 143, 200, 286, 300, 400, 429, 500,
      571, 600, 700, 714, 800, 857, 900, 950, 990, 999, 1000};

  // Gather and deduplicate silhouette contacts across all sample views
  std::vector<ContactInfo> all_contacts;
  for (const auto &view : sample_views) {
    std::vector<ContactInfo> raw = GenerateSilhouetteContacts(view, fine_mixes);
    for (const auto &c : raw) {
      bool dup = false;
      for (const auto &ex : all_contacts) {
        if (ex.vertex == c.vertex &&
            ex.edge_start == c.edge_start &&
            ex.edge_finish == c.edge_finish &&
            ex.edge_start2 == c.edge_start2 &&
            ex.edge_finish2 == c.edge_finish2 &&
            ex.mix == c.mix) {
          dup = true;
          break;
        }
      }
      if (!dup) all_contacts.push_back(c);
    }
  }

  std::vector<CandidateTriple> all_cands = GenerateCandidateTriples(tri, all_contacts, screen_support_error);

  // Score candidates by how strongly they oppose unit_n (maximizing a · (-unit_n), so a · unit_n < 0)
  struct ScoredTriple {
    double score;
    CandidateTriple triple;
  };

  std::vector<ScoredTriple> opposing;
  for (const auto &c : all_cands) {
    double dot = yocto::dot(c.normalized_a, unit_n);
    if (dot < 0.0) {
      opposing.push_back({-dot, c}); // score is positive magnitude opposing n
    }
  }

  std::sort(opposing.begin(), opposing.end(), [](const ScoredTriple &a, const ScoredTriple &b) {
    return a.score > b.score;
  });

  // Keep top unique candidates by normalized_a
  std::vector<CandidateTriple> result;
  for (const auto &st : opposing) {
    bool dup = false;
    for (const auto &r : result) {
      if (yocto::length(r.normalized_a - st.triple.normalized_a) < 1e-6) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      result.push_back(st.triple);
      if ((int)result.size() >= max_candidates) break;
    }
  }
  return result;
}

bool Tube229::PointInTetrahedron(
    const vec3 &p, const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3,
    double *out_margin) {
  auto orient = [](const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d) {
    return yocto::dot(a - d, yocto::cross(b - d, c - d));
  };
  double d0 = orient(v0, v1, v2, p);
  double d1 = orient(v0, v2, v3, p);
  double d2 = orient(v0, v3, v1, p);
  double d3 = orient(v3, v2, v1, p);
  bool all_pos = (d0 > 1e-14 && d1 > 1e-14 && d2 > 1e-14 && d3 > 1e-14);
  bool all_neg = (d0 < -1e-14 && d1 < -1e-14 && d2 < -1e-14 && d3 < -1e-14);
  if (!all_pos && !all_neg) return false;

  if (out_margin) {
    auto dist_to_face = [](const vec3 &a, const vec3 &b, const vec3 &c) {
      vec3 n = yocto::cross(b - a, c - a);
      double len = yocto::length(n);
      if (len < 1e-14) return 0.0;
      return std::abs(yocto::dot(n, a)) / len;
    };
    *out_margin = std::min({
      dist_to_face(v0, v1, v2),
      dist_to_face(v0, v2, v3),
      dist_to_face(v0, v3, v1),
      dist_to_face(v1, v2, v3)
    });
  }
  return true;
}

struct ClosestResult {
  double key = 1e30;
  std::vector<int> support;
  vec3 point = {0, 0, 0};
};

static ClosestResult ClosestOriginPoint(const std::vector<vec3> &pts, const std::vector<int> &indices) {
  ClosestResult best{1e30, {}, {0, 0, 0}};

  auto consider = [&](const std::vector<int> &supp, const std::vector<double> &coeffs) {
    vec3 pt = {0, 0, 0};
    for (size_t i = 0; i < supp.size(); i++) {
      pt = pt + pts[supp[i]] * coeffs[i];
    }
    double k = yocto::dot(pt, pt);
    if (k < best.key) {
      best = {k, supp, pt};
    }
  };

  for (int idx : indices) consider({idx}, {1.0});

  int m = indices.size();
  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      int idx_a = indices[i], idx_b = indices[j];
      vec3 a = pts[idx_a], b = pts[idx_b];
      vec3 dir = b - a;
      double den = yocto::dot(dir, dir);
      if (den <= 1e-30) continue;
      double t = -yocto::dot(a, dir) / den;
      if (t > 1e-12 && t < 1.0 - 1e-12) {
        consider({idx_a, idx_b}, {1.0 - t, t});
      }
    }
  }

  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      for (int k = j + 1; k < m; k++) {
        int idx_a = indices[i], idx_b = indices[j], idx_c = indices[k];
        vec3 a = pts[idx_a], b = pts[idx_b], c = pts[idx_c];
        vec3 u = b - a;
        vec3 v = c - a;
        double uu = yocto::dot(u, u), uv = yocto::dot(u, v), vv = yocto::dot(v, v);
        double det = uu * vv - uv * uv;
        if (det <= 1e-30) continue;
        double au = yocto::dot(a, u), av = yocto::dot(a, v);
        double s = (-au * vv + av * uv) / det;
        double t = (-av * uu + au * uv) / det;
        if (s > 1e-12 && t > 1e-12 && (s + t) < 1.0 - 1e-12) {
          consider({idx_a, idx_b, idx_c}, {1.0 - s - t, s, t});
        }
      }
    }
  }
  return best;
}

bool Tube229::ClosestOriginFace(
    const std::vector<CandidateTriple> &candidates,
    const std::array<int, 4> &simplex,
    std::array<int, 3> *out_face,
    vec3 *out_normal) {
  std::vector<vec3> pts = {
    candidates[simplex[0]].normalized_a,
    candidates[simplex[1]].normalized_a,
    candidates[simplex[2]].normalized_a,
    candidates[simplex[3]].normalized_a
  };
  std::vector<int> indices = {0, 1, 2, 3};
  ClosestResult res = ClosestOriginPoint(pts, indices);
  if (res.support.size() == 3) {
    *out_face = {simplex[res.support[0]], simplex[res.support[1]], simplex[res.support[2]]};
    *out_normal = res.point;
    return true;
  }
  return false;
}

bool Tube229::FindBalancedTetrahedron(
    const std::vector<vec3> &pts,
    std::array<int, 4> *out_simplex,
    vec3 *out_separating_normal) {
  int n = pts.size();
  if (n < 4) return false;

  int start = 0;
  double min_norm = yocto::dot(pts[0], pts[0]);
  for (int i = 1; i < n; i++) {
    double d = yocto::dot(pts[i], pts[i]);
    if (d < min_norm) { min_norm = d; start = i; }
  }

  std::vector<int> active = {start};
  std::set<std::pair<std::vector<int>, int>> seen;
  vec3 last_current = pts[start];

  for (int iter = 0; iter < 100; iter++) {
    if (active.size() >= 4) {
      int m = active.size();
      for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
          for (int k = j + 1; k < m; k++) {
            for (int l = k + 1; l < m; l++) {
              double margin = 0;
              if (PointInTetrahedron(vec3{0, 0, 0}, pts[active[i]], pts[active[j]], pts[active[k]], pts[active[l]], &margin) && margin > 1e-10) {
                *out_simplex = {active[i], active[j], active[k], active[l]};
                return true;
              }
            }
          }
        }
      }
    }

    ClosestResult closest = ClosestOriginPoint(pts, active);
    if (closest.support.empty()) {
      if (out_separating_normal) *out_separating_normal = last_current;
      return false;
    }
    active = closest.support;
    vec3 current = closest.point;
    last_current = current;
    double norm_sq = closest.key;

    int next_index = -1;
    double min_dot = 1e30;
    for (int i = 0; i < n; i++) {
      double d = yocto::dot(current, pts[i]);
      if (d < min_dot) { min_dot = d; next_index = i; }
    }
    double improvement = norm_sq - min_dot;
    if (improvement <= 1e-13 * std::max(1.0, norm_sq)) {
      if (out_separating_normal) *out_separating_normal = current;
      return false;
    }

    if (std::find(active.begin(), active.end(), next_index) != active.end()) {
      if (out_separating_normal) *out_separating_normal = current;
      return false;
    }

    std::vector<int> sorted_active = active;
    std::sort(sorted_active.begin(), sorted_active.end());
    if (seen.count({sorted_active, next_index})) {
      if (out_separating_normal) *out_separating_normal = current;
      return false;
    }
    seen.insert({sorted_active, next_index});
    active.push_back(next_index);
  }
  if (out_separating_normal) *out_separating_normal = last_current;
  return false;
}

bool Tube229::FindBalancedTetrahedron(
    const std::vector<CandidateTriple> &candidates,
    std::array<int, 4> *out_simplex,
    vec3 *out_separating_normal) {
  int n = candidates.size();
  if (n < 4) return false;
  std::vector<vec3> pts(n);
  for (int i = 0; i < n; i++) pts[i] = candidates[i].normalized_a;
  return FindBalancedTetrahedron(pts, out_simplex, out_separating_normal);
}

bool Tube229::FindExtremalTetrahedron(
    const std::vector<vec3> &pts,
    std::array<int, 4> *out_indices) {
  int n = pts.size();
  if (n < 4) return false;
  const double inv_sqrt3 = 1.0 / std::sqrt(3.0);
  const vec3 base_t[4] = {
    { inv_sqrt3,  inv_sqrt3,  inv_sqrt3},
    { inv_sqrt3, -inv_sqrt3, -inv_sqrt3},
    {-inv_sqrt3,  inv_sqrt3, -inv_sqrt3},
    {-inv_sqrt3, -inv_sqrt3,  inv_sqrt3}
  };

  std::mt19937 rng(12345);
  std::normal_distribution<double> gauss(0.0, 1.0);

  double best_margin = -1.0;
  std::array<int, 4> best_indices = {-1, -1, -1, -1};

  for (int trial = 0; trial < 400; trial++) {
    vec3 v0 = {gauss(rng), gauss(rng), gauss(rng)};
    double l0 = yocto::length(v0);
    if (l0 < 1e-6) continue;
    v0 = v0 / l0;

    vec3 v1 = {gauss(rng), gauss(rng), gauss(rng)};
    v1 = v1 - v0 * yocto::dot(v0, v1);
    double l1 = yocto::length(v1);
    if (l1 < 1e-6) continue;
    v1 = v1 / l1;

    vec3 v2 = yocto::cross(v0, v1);

    vec3 u[4];
    for (int k = 0; k < 4; k++) {
      u[k] = v0 * base_t[k].x + v1 * base_t[k].y + v2 * base_t[k].z;
    }

    int idx[4];
    bool dup = false;
    for (int k = 0; k < 4; k++) {
      double max_dot = -1e30;
      int best_i = -1;
      for (int i = 0; i < n; i++) {
        double d = yocto::dot(pts[i], u[k]);
        if (d > max_dot) { max_dot = d; best_i = i; }
      }
      idx[k] = best_i;
      for (int prev = 0; prev < k; prev++) {
        if (idx[prev] == best_i) { dup = true; break; }
      }
      if (dup) break;
    }
    if (dup) continue;

    double margin = 0;
    if (PointInTetrahedron(vec3{0, 0, 0}, pts[idx[0]], pts[idx[1]], pts[idx[2]], pts[idx[3]], &margin) && margin > best_margin) {
      best_margin = margin;
      best_indices = {idx[0], idx[1], idx[2], idx[3]};
    }
  }
  if (best_margin > 1e-10) {
    *out_indices = best_indices;
    return true;
  }
  return false;
}

bool Tube229::FindExtremalTetrahedron(
    const std::vector<CandidateTriple> &candidates,
    std::array<int, 4> *out_indices) {
  int n = candidates.size();
  if (n < 4) return false;
  std::vector<vec3> pts(n);
  for (int i = 0; i < n; i++) pts[i] = candidates[i].normalized_a;
  return FindExtremalTetrahedron(pts, out_indices);
}

bool Tube229::RefinePoolCuttingPlane(
    const std::vector<vec3> &pts,
    std::set<int> *in_out_pool,
    std::array<int, 4> *out_simplex,
    double *out_margin,
    int max_iters) {
  if (!in_out_pool || !out_simplex) return false;

  for (int iter = 0; iter < max_iters; iter++) {
    std::vector<int> cur_pool(in_out_pool->begin(), in_out_pool->end());
    ClosestResult closest = ClosestOriginPoint(pts, cur_pool);
    vec3 v = closest.point;
    if (closest.key < 1e-12) {
      if (closest.support.size() == 3) {
        int i0 = closest.support[0], i1 = closest.support[1], i2 = closest.support[2];
        vec3 face_norm = yocto::cross(pts[i1] - pts[i0], pts[i2] - pts[i0]);
        double len = yocto::length(face_norm);
        if (len > 1e-9) {
          face_norm = face_norm / len;
          int best_pos = -1, best_neg = -1;
          double max_pos = -1e30, max_neg = -1e30;
          for (size_t i = 0; i < pts.size(); i++) {
            double dp = yocto::dot(pts[i], face_norm);
            if (dp > max_pos) { max_pos = dp; best_pos = i; }
            double dn = yocto::dot(pts[i], -face_norm);
            if (dn > max_neg) { max_neg = dn; best_neg = i; }
          }
          if (best_pos >= 0 && best_neg >= 0 && max_pos > 1e-9 && max_neg > 1e-9 && best_pos != best_neg) {
            int tri_edges[3][2] = {{i0, i1}, {i1, i2}, {i2, i0}};
            for (int e = 0; e < 3; e++) {
              int e0 = tri_edges[e][0], e1 = tri_edges[e][1];
              if (best_pos == e0 || best_pos == e1 || best_neg == e0 || best_neg == e1) continue;
              double m = 0;
              if (PointInTetrahedron(vec3{0, 0, 0}, pts[e0], pts[e1], pts[best_pos], pts[best_neg], &m) && m > 1e-12) {
                *out_simplex = {e0, e1, best_pos, best_neg};
                in_out_pool->insert(best_pos);
                in_out_pool->insert(best_neg);
                if (out_margin) *out_margin = m;
                return true;
              }
            }
            // Also directly test the face {i0, i1, i2} with best_neg
            if (best_neg != i0 && best_neg != i1 && best_neg != i2) {
              double m = 0;
              if (PointInTetrahedron(vec3{0, 0, 0}, pts[i0], pts[i1], pts[i2], pts[best_neg], &m) && m > 1e-12) {
                *out_simplex = {i0, i1, i2, best_neg};
                in_out_pool->insert(best_neg);
                if (out_margin) *out_margin = m;
                return true;
              }
            }
          }

          // Do not prematurely early return when normal piercing fails to cage origin.
          // Orient face normal so active pool is on the positive side, and continue in direction -v.
          double sum_d = 0;
          for (int p_idx : cur_pool) sum_d += yocto::dot(pts[p_idx], face_norm);
          if (sum_d < 0) face_norm = -face_norm;
          v = face_norm;
        }
      } else {
        double vlen = yocto::length(v);
        if (vlen > 1e-15) v = v / vlen;
      }
    }

    int best_i = -1;
    double max_dot = -1e30;
    for (size_t i = 0; i < pts.size(); i++) {
      double d = yocto::dot(pts[i], -v);
      if (d > max_dot) { max_dot = d; best_i = i; }
    }
    if (max_dot <= 1e-12 || in_out_pool->count(best_i)) break;
    in_out_pool->insert(best_i);

    for (size_t i = 0; i < cur_pool.size(); i++) {
      for (size_t j = i + 1; j < cur_pool.size(); j++) {
        for (size_t k = j + 1; k < cur_pool.size(); k++) {
          double m = 0;
          if (PointInTetrahedron(vec3{0, 0, 0}, pts[cur_pool[i]], pts[cur_pool[j]], pts[cur_pool[k]], pts[best_i], &m) && m > 1e-12) {
            *out_simplex = {cur_pool[i], cur_pool[j], cur_pool[k], best_i};
            if (out_margin) *out_margin = m;
            return true;
          }
        }
      }
    }
  }
  return false;
}


// ============================================================================
// EXACT POLYNOMIAL AND AUDIT ARITHMETIC
// ============================================================================

struct QPoly {
  BigRat c[10];
  QPoly() {
    for (int i = 0; i < 10; i++) c[i] = BigRat(0);
  }
  static QPoly MulLinear(const BigVecQ3 &a, const BigVecQ3 &b) {
    QPoly p;
    p.c[4] = a.x * b.x;
    p.c[5] = a.x * b.y + a.y * b.x;
    p.c[6] = a.x * b.z + a.z * b.x;
    p.c[7] = a.y * b.y;
    p.c[8] = a.y * b.z + a.z * b.y;
    p.c[9] = a.z * b.z;
    return p;
  }
  void AddScaled(const BigRat &s, const QPoly &o) {
    for (int i = 0; i < 10; i++) c[i] += s * o.c[i];
  }
  std::pair<BigRat, BigRat> EvalCentered(const BigVecQ3 &center, const BigVecQ3 &radius) const {
    BigRat val = c[0] + c[1] * center.x + c[2] * center.y + c[3] * center.z +
                 c[4] * center.x * center.x + c[5] * center.x * center.y +
                 c[6] * center.x * center.z + c[7] * center.y * center.y +
                 c[8] * center.y * center.z + c[9] * center.z * center.z;

    BigRat grad_x = c[1] + BigRat(2) * c[4] * center.x + c[5] * center.y + c[6] * center.z;
    BigRat grad_y = c[2] + c[5] * center.x + BigRat(2) * c[7] * center.y + c[8] * center.z;
    BigRat grad_z = c[3] + c[6] * center.x + c[8] * center.y + BigRat(2) * c[9] * center.z;

    auto abs_r = [](const BigRat &x) { return x < 0 ? -x : x; };

    BigRat lin_bound = abs_r(grad_x) * radius.x + abs_r(grad_y) * radius.y + abs_r(grad_z) * radius.z;
    BigRat quad_bound = abs_r(c[4]) * radius.x * radius.x + abs_r(c[5]) * radius.x * radius.y +
                        abs_r(c[6]) * radius.x * radius.z + abs_r(c[7]) * radius.y * radius.y +
                        abs_r(c[8]) * radius.y * radius.z + abs_r(c[9]) * radius.z * radius.z;
    return {val, lin_bound + quad_bound};
  }
};

static inline BigRat CeilTo(const BigRat &x, const BigInt &denom) {
  BigRat scaled = x * BigRat(denom);
  BigInt num = scaled.Numerator();
  BigInt den = scaled.Denominator();
  BigInt q;
  if (num >= BigInt(0)) {
    q = (num + den - BigInt(1)) / den;
  } else {
    q = num / den;
  }
  return BigRat(q, denom);
}

static inline BigRat CeilTo(const BigRat &x, int64_t denom) {
  return CeilTo(x, BigInt(denom));
}

static inline BigRat FloorTo(const BigRat &x, const BigInt &denom) {
  BigRat scaled = x * BigRat(denom);
  BigInt num = scaled.Numerator();
  BigInt den = scaled.Denominator();
  BigInt q;
  if (num >= BigInt(0)) {
    q = num / den;
  } else {
    q = (num - den + BigInt(1)) / den;
  }
  return BigRat(q, denom);
}

static inline BigRat FloorTo(const BigRat &x, int64_t denom) {
  return FloorTo(x, BigInt(denom));
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

BigRat Tube229::ExactTetrahedronAxisRadius(const BigVecQ3 pts[4]) {
  BigRat zero[4];
  if (!Barycentric4(pts, {BigRat(0), BigRat(0), BigRat(0)}, zero)) return BigRat(0);
  for (int i = 0; i < 4; i++) {
    if (zero[i] <= 0) return BigRat(0);
  }
  BigRat min_bound(1000000);
  for (int axis = 0; axis < 3; axis++) {
    for (int sign : {-1, 1}) {
      BigVecQ3 target(axis == 0 ? BigRat(sign) : BigRat(0),
                   axis == 1 ? BigRat(sign) : BigRat(0),
                   axis == 2 ? BigRat(sign) : BigRat(0));
      BigRat at_one[4];
      if (!Barycentric4(pts, target, at_one)) continue;
      for (int i = 0; i < 4; i++) {
        BigRat d = at_one[i] - zero[i];
        if (d < 0) {
          BigRat b = zero[i] / (-d);
          if (b < min_bound) min_bound = b;
        }
      }
    }
  }
  return min_bound;
}

bool Tube229::AuditAxis(
    const TriangleQ &tri, ContactInfo contacts[3], AxisCertificate *out_cert,
    BigVecQ3 *out_center, BigRat *out_delta, std::string *fail_reason,
    const BigRat &max_allowed_defect) {
  BigVecQ3 edges[3] = {GetExactEdge(contacts[0]), GetExactEdge(contacts[1]), GetExactEdge(contacts[2])};
  BigVecQ3 coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
  BigVecQ3 coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
  BigVecQ3 coeff2 = BigVecQ3::Cross(edges[0], edges[1]);

  BigRat p0 = BigVecQ3::Dot(tri.corners[0], coeff0);
  BigRat p1 = BigVecQ3::Dot(tri.corners[0], coeff1);
  BigRat p2 = BigVecQ3::Dot(tri.corners[0], coeff2);
  if (p0 < 0 && p1 < 0 && p2 < 0) {
    std::swap(contacts[1], contacts[2]);
    std::swap(edges[1], edges[2]);
    coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
    coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
    coeff2 = BigVecQ3::Cross(edges[0], edges[1]);
  }

  BigVecQ3 w_coeffs[3] = {coeff0, coeff1, coeff2};
  BigRat support_error(6, 1000000000000000LL); // 6 / 10^15
  BigRat weight_upper[3];
  BigRat sum_weight_upper(0);

  for (int m = 0; m < 3; m++) {
    BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
    BigRat w_min = w_max;
    for (int c = 1; c < 3; c++) {
      BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
      if (val > w_max) w_max = val;
      if (val < w_min) w_min = val;
    }
    if (w_min < support_error) {
      if (fail_reason)
        *fail_reason =
          std::format("w_min < support_error (m={}, w_min={})",
                      m, w_min.ToString());
      return false;
    }
    weight_upper[m] = w_max + support_error;
    sum_weight_upper = sum_weight_upper + weight_upper[m];
  }

  BigRat exact_B = sum_weight_upper * BigRat(2);
  BigRat B = CeilTo(exact_B, 1000000000LL);
  if (B <= 0) {
    if (fail_reason) *fail_reason = "B <= 0";
    return false;
  }

  out_cert->B = B;
  for (int m = 0; m < 3; m++) {
    out_cert->contacts[m] = contacts[m];
    int sel = contacts[m].vertex;
    BigVecQ3 v_sel = VertexQ(sel);
    BigRat best_support(1000000);
    int best_w = -1;
    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (contacts[m].mix == 1000 && sel == contacts[m].edge_finish && k == contacts[m].edge_start) ||
                 (contacts[m].mix == 0 && sel == contacts[m].edge_start2 && k == contacts[m].edge_finish2);
      BigRat s_upper(0);
      if (!tie) {
        BigVecQ3 v_k = VertexQ(k);
        BigVecQ3 delta = v_k - v_sel;
        BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta);
        BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
          if (val > max_s) max_s = val;
        }
        s_upper = max_s + support_error;
      }
      if (s_upper > max_allowed_defect) {
        if (fail_reason) *fail_reason = StringPrintf("s_upper > %s (m=%d, k=%d, s=%s)", max_allowed_defect.ToString().c_str(), m, k, s_upper.ToString().c_str());
        return false;
      }
      if (s_upper < best_support) {
        best_support = s_upper;
        best_w = k;
      }
    }
    if (best_support >= 0) {
      if (fail_reason) *fail_reason = StringPrintf("best_support >= 0 (m=%d)", m);
      return false;
    }
    out_cert->nonzero_witness[m] = best_w;
  }

  BigVecQ3 ball_center, ball_radius;
  for (int c = 0; c < 3; c++) {
    BigRat c0 = (c == 0 ? tri.corners[0].x : c == 1 ? tri.corners[0].y : tri.corners[0].z);
    BigRat c1 = (c == 0 ? tri.corners[1].x : c == 1 ? tri.corners[1].y : tri.corners[1].z);
    BigRat c2 = (c == 0 ? tri.corners[2].x : c == 1 ? tri.corners[2].y : tri.corners[2].z);
    BigRat lo = std::min({c0, c1, c2});
    BigRat hi = std::max({c0, c1, c2});
    BigRat mid = (lo + hi) / BigRat(2);
    BigRat rad = (hi - lo) / BigRat(2);
    if (c == 0) { ball_center.x = mid; ball_radius.x = rad; }
    else if (c == 1) { ball_center.y = mid; ball_radius.y = rad; }
    else { ball_center.z = mid; ball_radius.z = rad; }
  }

  QPoly polys[3];
  for (int coord = 0; coord < 3; coord++) {
    for (int i = 0; i < 3; i++) {
      BigVecQ3 v_supp = VertexQ(contacts[i].vertex);
      BigVecQ3 lift_row[3] = {
        {BigRat(0), edges[i].z, -edges[i].y},
        {-edges[i].z, BigRat(0), edges[i].x},
        {edges[i].y, -edges[i].x, BigRat(0)}
      };
      BigVecQ3 cross_lift;
      if (coord == 0) {
        cross_lift = {v_supp.y * lift_row[2].x - v_supp.z * lift_row[1].x,
                      v_supp.y * lift_row[2].y - v_supp.z * lift_row[1].y,
                      v_supp.y * lift_row[2].z - v_supp.z * lift_row[1].z};
      } else if (coord == 1) {
        cross_lift = {v_supp.z * lift_row[0].x - v_supp.x * lift_row[2].x,
                      v_supp.z * lift_row[0].y - v_supp.x * lift_row[2].y,
                      v_supp.z * lift_row[0].z - v_supp.x * lift_row[2].z};
      } else {
        cross_lift = {v_supp.x * lift_row[1].x - v_supp.y * lift_row[0].x,
                      v_supp.x * lift_row[1].y - v_supp.y * lift_row[0].y,
                      v_supp.x * lift_row[1].z - v_supp.y * lift_row[0].z};
      }
      QPoly term = QPoly::MulLinear(w_coeffs[i], cross_lift);
      polys[coord].AddScaled(BigRat(1), term);
    }
  }

  std::pair<BigRat, BigRat> evals[3] = {
    polys[0].EvalCentered(ball_center, ball_radius),
    polys[1].EvalCentered(ball_center, ball_radius),
    polys[2].EvalCentered(ball_center, ball_radius)
  };

  out_center->x = evals[0].first / B;
  out_center->y = evals[1].first / B;
  out_center->z = evals[2].first / B;

  BigRat variation_error(150, 10000000000LL); // 150 * KAPPA
  BigRat exact_delta = (evals[0].second + evals[1].second + evals[2].second + BigRat(3) * variation_error) / B;
  *out_delta = CeilTo(exact_delta, 1000000000LL);
  return true;
}

static const BigRat CANDIDATE_RS[] = {
  BigRat("1/1000"), BigRat("1/2000"), BigRat("1/4000"),
  BigRat("1/5000"), BigRat("1/8000"), BigRat("1/10000"),
  BigRat("1/20000"), BigRat("1/40000"), BigRat("1/50000"),
  BigRat("1/100000"), BigRat("1/200000"), BigRat("1/250000"),
  BigRat("1/300000"), BigRat("1/400000"), BigRat("1/500000"),
  BigRat("1/1000000"), BigRat("1/2000000"), BigRat("1/3000000"),
  BigRat("1/4000000"), BigRat("1/5000000"), BigRat("1/6000000"),
  BigRat("1/8000000"), BigRat("1/10000000"), BigRat("1/20000000"),
  BigRat("1/50000000"), BigRat("1/100000000"),
  BigRat("1/200000000"), BigRat("1/500000000"),
  BigRat("1/1000000000"), BigRat("1/2000000000"),
  BigRat("1/5000000000"), BigRat("1/10000000000"),
  BigRat("1/20000000000"), BigRat("1/50000000000"),
  BigRat("1/100000000000"), BigRat("1/200000000000"), BigRat("1/500000000000"),
  BigRat("1/1000000000000"), BigRat("1/2000000000000"), BigRat("1/5000000000000"),
  BigRat("1/10000000000000"), BigRat("1/20000000000000"), BigRat("1/50000000000000"),
  BigRat("1/100000000000000"), BigRat("1/200000000000000"), BigRat("1/500000000000000"),
  BigRat("1/1000000000000000"), BigRat("1/2000000000000000"), BigRat("1/5000000000000000"),
  BigRat("1/10000000000000000"), BigRat("1/20000000000000000"), BigRat("1/50000000000000000"),
  BigRat("1/100000000000000000"), BigRat("1/200000000000000000"), BigRat("1/500000000000000000"),
  BigRat("1/1000000000000000000"), BigRat("1/2000000000000000000"), BigRat("1/5000000000000000000"),
  BigRat("1/10000000000000000000"), BigRat("1/20000000000000000000"), BigRat("1/50000000000000000000"),
  BigRat("1/100000000000000000000"), BigRat("1/200000000000000000000"), BigRat("1/500000000000000000000"),
  BigRat("1/1000000000000000000000"), BigRat("1/10000000000000000000000"),
  BigRat("1/100000000000000000000000"), BigRat("1/1000000000000000000000000"),
  BigRat("1/10000000000000000000000000") // 1e-25
};

bool Tube229::AuditCertificateAdaptive(
    const TriangleQ &tri,
    const TubeCertificate &in_cert,
    TubeCertificate *out_cert,
    std::string *fail_reason) {

  *out_cert = in_cert;
  BigVecQ3 centers[4];
  BigRat deltas[4];
  for (int a = 0; a < 4; a++) {
    ContactInfo contacts[3] = {in_cert.axes[a].contacts[0],
                               in_cert.axes[a].contacts[1],
                               in_cert.axes[a].contacts[2]};
    std::string axis_reason;
    if (!AuditAxis(tri, contacts, &out_cert->axes[a], &centers[a], &deltas[a], &axis_reason)) {
      if (fail_reason) *fail_reason = StringPrintf("axis %d audit failed: %s", a, axis_reason.c_str());
      return false;
    }
  }

  BigRat delta = std::max({deltas[0], deltas[1], deltas[2], deltas[3]});
  BigRat axis_radius = ExactTetrahedronAxisRadius(centers);
  BigRat cover_radius = axis_radius * BigRat(19, 20) * BigRat(4, 7);
  BigRat diff = cover_radius - delta;
  if (diff <= BigRat(0)) {
    if (fail_reason) *fail_reason = StringPrintf("cover_radius - delta <= 0 (diff=%s, cover=%s, delta=%s)",
                                                 diff.ToString().c_str(), cover_radius.ToString().c_str(), delta.ToString().c_str());
    return false;
  }
  BigRat c = FloorTo(diff, BigInt(1000000000LL));
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt(1000000000000LL));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt(1000000000000000LL));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = diff / BigRat(2);
  }
  if (c <= BigRat(0)) {
    if (fail_reason) *fail_reason = StringPrintf("c <= 0 after high precision floor (diff=%s)",
                                                 diff.ToString().c_str());
    return false;
  }

  BigRat scale = (c + delta) * BigRat(7, 4);
  for (int axis = 0; axis < 3; axis++) {
    for (int sign : {-1, 1}) {
      BigVecQ3 target(axis == 0 ? scale * BigRat(sign) : BigRat(0),
                      axis == 1 ? scale * BigRat(sign) : BigRat(0),
                      axis == 2 ? scale * BigRat(sign) : BigRat(0));
      BigRat lam[4];
      if (!Barycentric4(centers, target, lam)) {
        if (fail_reason) *fail_reason = "Barycentric4 degenerate";
        return false;
      }
      for (int i = 0; i < 4; i++) {
        if (lam[i] < 0) {
          if (fail_reason) *fail_reason = StringPrintf("target axis %d sign %d not inside (lam[%d]=%s)",
                                                       axis, sign, i, lam[i].ToString().c_str());
          return false;
        }
      }
    }
  }

  BigRat certified_r(0);
  for (const auto &cand : CANDIDATE_RS) {
    if (cand * cand * (BigRat(1) + c * c) <= BigRat(4) * c * c) {
      certified_r = cand;
      break;
    }
  }
  if (certified_r <= BigRat(0) && c > BigRat(0)) {
    // Dynamic fallback: for any c in (0, 1), r = c/2 strictly satisfies:
    // r^2 (1 + c^2) = (c^2 / 4) * (1 + c^2) <= c^2 / 2 < 4 * c^2.
    BigRat cand = c / BigRat(2);
    if (cand * cand * (BigRat(1) + c * c) <= BigRat(4) * c * c) {
      certified_r = cand;
    }
  }
  if (certified_r <= BigRat(0)) {
    if (fail_reason) *fail_reason = "No candidate radius satisfies angle bound";
    return false;
  }

  out_cert->c = c;
  out_cert->delta = delta;
  out_cert->r = certified_r;
  return true;
}

// Helper to deduplicate ContactInfo entries
static void AddContactDeduplicated(std::vector<ContactInfo> *dest, const ContactInfo &c) {
  for (const auto &ex : *dest) {
    if (ex.vertex == c.vertex &&
        ex.edge_start == c.edge_start &&
        ex.edge_finish == c.edge_finish &&
        ex.edge_start2 == c.edge_start2 &&
        ex.edge_finish2 == c.edge_finish2 &&
        ex.mix == c.mix) {
      return;
    }
  }
  dest->push_back(c);
}

// Helper to deduplicate CandidateTriple entries
static bool AddCandidateDeduplicated(std::vector<Tube229::CandidateTriple> *dest, const Tube229::CandidateTriple &c) {
  for (const auto &ex : *dest) {
    if (yocto::length(ex.normalized_a - c.normalized_a) < 1e-6) {
      return false;
    }
  }
  dest->push_back(c);
  return true;
}

// Fast single-view synthesis for easy leaves:
// Evaluates silhouette contacts at centroid only, tests balanced tet on well-conditioned
// candidates (B >= 0.8) and full candidate pool, with a one-shot targeted opposing search fallback.
bool Tube229::SynthesizeCertificateFast(
    const TriangleQ &tri,
    int depth,
    TubeCertificate *out_cert,
    const std::vector<ContactInfo> &extra_contacts,
    const std::vector<CandidateTriple> &extra_axes) {

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  // Single-view silhouette sampling at centroid with standard cone samples
  std::vector<int> std_mixes = {0, 1, 143, 286, 429, 571, 714, 857, 999, 1000};
  std::vector<ContactInfo> contacts = GenerateSilhouetteContacts(centroid, std_mixes);
  for (const auto &ec : extra_contacts) {
    AddContactDeduplicated(&contacts, ec);
  }

  std::vector<CandidateTriple> candidates = GenerateCandidateTriples(tri, contacts, 1e-12);
  for (const auto &ea : extra_axes) {
    AddCandidateDeduplicated(&candidates, ea);
  }

  if (candidates.size() < 4) return false;

  // 1. Try well-conditioned candidates (B >= 0.8) first to minimize delta variation
  std::vector<CandidateTriple> good_b;
  for (const auto &c : candidates) {
    if (c.B >= 0.8) good_b.push_back(c);
  }
  if (good_b.size() >= 4) {
    std::array<int, 4> simplex;
    if (FindBalancedTetrahedron(good_b, &simplex)) {
      TubeCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = good_b[simplex[a]].contacts[0];
        test_cert.axes[a].contacts[1] = good_b[simplex[a]].contacts[1];
        test_cert.axes[a].contacts[2] = good_b[simplex[a]].contacts[2];
      }
      if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
        return true;
      }
    }
  }

  // 2. Try all candidates
  std::array<int, 4> simplex;
  vec3 oppose_dir = {0, 0, 0};
  if (FindBalancedTetrahedron(candidates, &simplex, &oppose_dir)) {
    TubeCertificate test_cert;
    for (int a = 0; a < 4; a++) {
      test_cert.axes[a].contacts[0] = candidates[simplex[a]].contacts[0];
      test_cert.axes[a].contacts[1] = candidates[simplex[a]].contacts[1];
      test_cert.axes[a].contacts[2] = candidates[simplex[a]].contacts[2];
    }
    if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
      return true;
    }
  }

  // 3. One-shot targeted opposing search fallback
  if (yocto::length(oppose_dir) > 1e-12) {
    std::vector<CandidateTriple> opposing = FindOpposingCandidates(tri, oppose_dir, 50, 1e-12);
    for (const auto &opp : opposing) {
      AddCandidateDeduplicated(&candidates, opp);
    }

    if (FindBalancedTetrahedron(candidates, &simplex)) {
      TubeCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = candidates[simplex[a]].contacts[0];
        test_cert.axes[a].contacts[1] = candidates[simplex[a]].contacts[1];
        test_cert.axes[a].contacts[2] = candidates[simplex[a]].contacts[2];
      }
      if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
        return true;
      }
    }
  }

  return false;
}

// Powerful multi-view & iterative cutting-plane synthesis for hard / canyon leaves:
// 1. Evaluates silhouette contacts across 4 distinct view angles (centroid + 3 corners of tri)
//    to capture view-dependent silhouette edges across the entire spherical region.
// 2. Uses a rich mix permille grid to cover boundary transitions and critical tangents.
// 3. Executes an iterative cutting-plane loop with Wolfe's algorithm and FindOpposingCandidates,
//    progressively querying opposing candidates in separating normal directions.
// 4. Incorporates RefinePoolCuttingPlane and regular extremal tetrahedron searches.
bool Tube229::SynthesizeCertificateIterative(
    const TriangleQ &tri,
    int depth,
    TubeCertificate *out_cert,
    const std::vector<ContactInfo> &extra_contacts,
    const std::vector<CandidateTriple> &extra_axes,
    int max_opposing_iters) {

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  // Multi-view generation: centroid AND all 3 corners of the spherical triangle
  std::vector<vec3> sample_views = {centroid, tri_f[0], tri_f[1], tri_f[2]};

  std::vector<CandidateTriple> candidates;
  for (const auto &view : sample_views) {
    auto v_cands = GenerateCandidatesForView(view, tri, /*evaluate_over_triangle=*/true, /*cone_samples=*/4, /*include_boundaries=*/false);
    for (const auto &c : v_cands) {
      AddCandidateDeduplicated(&candidates, c);
    }
  }

  // Also include extra_contacts if provided
  if (!extra_contacts.empty()) {
    auto ec_cands = GenerateCandidateTriples(tri, extra_contacts, 1e-12);
    for (const auto &c : ec_cands) {
      AddCandidateDeduplicated(&candidates, c);
    }
  }

  for (const auto &ea : extra_axes) {
    AddCandidateDeduplicated(&candidates, ea);
  }

  // If insufficient candidates, try higher cone sampling with boundary mixes
  if (candidates.size() < 4) {
    for (const auto &view : sample_views) {
      auto v_cands = GenerateCandidatesForView(view, tri, /*evaluate_over_triangle=*/true, /*cone_samples=*/10, /*include_boundaries=*/true);
      for (const auto &c : v_cands) {
        AddCandidateDeduplicated(&candidates, c);
      }
    }
  }

  if (candidates.size() < 4) return false;

  // Iterative cutting-plane loop:
  // In each round:
  //   a. Try well-conditioned candidates (B >= 0.8) with Wolfe
  //   b. Try all candidates with Wolfe
  //   c. Try cutting-plane pool refinement (RefinePoolCuttingPlane)
  //   d. If origin is not enclosed, query FindOpposingCandidates along separating normal
  for (int iter = 0; iter <= max_opposing_iters; iter++) {
    // 1. Try well-conditioned candidates (B >= 0.8)
    std::vector<CandidateTriple> good_b;
    for (const auto &c : candidates) {
      if (c.B >= 0.8) good_b.push_back(c);
    }
    if (good_b.size() >= 4) {
      std::array<int, 4> simplex;
      if (FindBalancedTetrahedron(good_b, &simplex)) {
        TubeCertificate test_cert;
        for (int a = 0; a < 4; a++) {
          test_cert.axes[a].contacts[0] = good_b[simplex[a]].contacts[0];
          test_cert.axes[a].contacts[1] = good_b[simplex[a]].contacts[1];
          test_cert.axes[a].contacts[2] = good_b[simplex[a]].contacts[2];
        }
        if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
          return true;
        }
      }
    }

    // 2. Try all candidates with Wolfe
    std::array<int, 4> simplex;
    vec3 sep_norm = {0, 0, 0};
    if (FindBalancedTetrahedron(candidates, &simplex, &sep_norm)) {
      TubeCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = candidates[simplex[a]].contacts[0];
        test_cert.axes[a].contacts[1] = candidates[simplex[a]].contacts[1];
        test_cert.axes[a].contacts[2] = candidates[simplex[a]].contacts[2];
      }
      if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
        return true;
      }
    }

    // 3. Try cutting-plane pool refinement on all candidates
    std::vector<vec3> pts(candidates.size());
    for (size_t i = 0; i < candidates.size(); i++) pts[i] = candidates[i].normalized_a;
    std::set<int> pool;
    for (size_t i = 0; i < candidates.size(); i++) pool.insert(i);
    std::array<int, 4> refine_simplex;
    double margin = 0;
    if (RefinePoolCuttingPlane(pts, &pool, &refine_simplex, &margin)) {
      TubeCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = candidates[refine_simplex[a]].contacts[0];
        test_cert.axes[a].contacts[1] = candidates[refine_simplex[a]].contacts[1];
        test_cert.axes[a].contacts[2] = candidates[refine_simplex[a]].contacts[2];
      }
      if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
        return true;
      }
    }

    // If reached max iterations or no valid separating direction, stop iterating
    if (iter == max_opposing_iters || yocto::length(sep_norm) < 1e-12) {
      break;
    }

    // 4. Query targeted opposing candidates opposing sep_norm
    std::vector<CandidateTriple> opposing = FindOpposingCandidates(tri, sep_norm, 50, 1e-12);
    if (opposing.empty()) break;

    bool added_any = false;
    for (const auto &opp : opposing) {
      if (AddCandidateDeduplicated(&candidates, opp)) {
        added_any = true;
      }
    }
    if (!added_any) break;
  }

  // 5. Scored candidate pool search:
  // Extract extreme vertices of candidate cloud, find all enclosing tetrahedra,
  // rank by margin (distance to origin), and audit top candidates.
  {
    std::vector<vec3> pts(candidates.size());
    for (size_t i = 0; i < candidates.size(); i++) pts[i] = candidates[i].normalized_a;

    std::set<int> pool_set;
    std::mt19937 dir_rng(42);
    std::normal_distribution<double> dir_dist(0.0, 1.0);
    for (int d = 0; d < 300; d++) {
      vec3 dir = {dir_dist(dir_rng), dir_dist(dir_rng), dir_dist(dir_rng)};
      double l = yocto::length(dir);
      if (l < 1e-12) continue;
      dir = dir / l;
      int best_hi = 0, best_lo = 0;
      double max_v = yocto::dot(pts[0], dir);
      double min_v = max_v;
      for (size_t i = 1; i < pts.size(); i++) {
        double v = yocto::dot(pts[i], dir);
        if (v > max_v) { max_v = v; best_hi = i; }
        if (v < min_v) { min_v = v; best_lo = i; }
      }
      pool_set.insert(best_hi);
      pool_set.insert(best_lo);
    }
    std::vector<int> pool(pool_set.begin(), pool_set.end());

    struct ScoredTet {
      double margin;
      std::array<int, 4> indices;
    };
    std::vector<ScoredTet> scored;

    int P = pool.size();
    if (P >= 4) {
      uint64_t comb4 = (uint64_t)P * (P - 1) * (P - 2) * (P - 3) / 24;
      if (comb4 <= 200000) {
        for (int i = 0; i < P; i++) {
          for (int j = i + 1; j < P; j++) {
            for (int k = j + 1; k < P; k++) {
              for (int l = k + 1; l < P; l++) {
                double margin = 0;
                if (PointInTetrahedron(vec3{0, 0, 0}, pts[pool[i]], pts[pool[j]], pts[pool[k]], pts[pool[l]], &margin) && margin > 1e-6) {
                  scored.push_back({margin, {pool[i], pool[j], pool[k], pool[l]}});
                }
              }
            }
          }
        }
      } else {
        std::mt19937 rng(1337 + depth * 31);
        std::uniform_int_distribution<int> dist(0, P - 1);
        for (int trial = 0; trial < 100000; trial++) {
          int i0 = dist(rng), i1 = dist(rng), i2 = dist(rng), i3 = dist(rng);
          if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
          double margin = 0;
          if (PointInTetrahedron(vec3{0, 0, 0}, pts[pool[i0]], pts[pool[i1]], pts[pool[i2]], pts[pool[i3]], &margin) && margin > 1e-6) {
            scored.push_back({margin, {pool[i0], pool[i1], pool[i2], pool[i3]}});
          }
        }
      }

      std::sort(scored.begin(), scored.end(), [](const ScoredTet &a, const ScoredTet &b) {
        return a.margin > b.margin;
      });

      for (size_t t = 0; t < std::min(scored.size(), (size_t)30); t++) {
        TubeCertificate test_cert;
        for (int a = 0; a < 4; a++) {
          test_cert.axes[a].contacts[0] = candidates[scored[t].indices[a]].contacts[0];
          test_cert.axes[a].contacts[1] = candidates[scored[t].indices[a]].contacts[1];
          test_cert.axes[a].contacts[2] = candidates[scored[t].indices[a]].contacts[2];
        }
        if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
          return true;
        }
      }
    }
  }

  // 6. Extremal regular tetrahedron orientation fallback
  std::array<int, 4> ext_simplex;
  if (FindExtremalTetrahedron(candidates, &ext_simplex)) {
    TubeCertificate test_cert;
    for (int a = 0; a < 4; a++) {
      test_cert.axes[a].contacts[0] = candidates[ext_simplex[a]].contacts[0];
      test_cert.axes[a].contacts[1] = candidates[ext_simplex[a]].contacts[1];
      test_cert.axes[a].contacts[2] = candidates[ext_simplex[a]].contacts[2];
    }
    if (AuditCertificateAdaptive(tri, test_cert, out_cert)) {
      return true;
    }
  }

  return false;
}

// General synthesis entry point:
// Tries Fast single-view synthesis first for efficiency.
// If Fast fails and !fast_only, escalates to powerful Multi-View Iterative cutting-plane search.
bool Tube229::SynthesizeCertificate(
    const TriangleQ &tri,
    int depth,
    TubeCertificate *out_cert,
    const std::vector<ContactInfo> &extra_contacts,
    const std::vector<CandidateTriple> &extra_axes,
    bool fast_only) {

  if (SynthesizeCertificateFast(tri, depth, out_cert, extra_contacts, extra_axes)) {
    return true;
  }
  if (fast_only) return false;

  return SynthesizeCertificateIterative(tri, depth, out_cert, extra_contacts, extra_axes, /*max_opposing_iters=*/5);
}

// ============================================================================
// DECOMPOSED & ANNULAR CERTIFICATE ROUTINES (THREE-WAY SPLIT THEOREM)
// ============================================================================

bool Tube229::FindHullSupportAxis(
    const TriangleQ &tri,
    AxisCertificate *out_cert,
    BigVecQ3 *out_center,
    BigRat *out_delta,
    std::string *fail_reason) {
  // 1. Compute view direction at centroid
  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  double vlen = yocto::length(centroid);
  if (vlen < 1e-12) {
    if (fail_reason) *fail_reason = "Centroid length < 1e-12";
    return false;
  }
  vec3 unit_view = centroid / vlen;

  // Coordinate frame for 2D projection
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

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> hull = ConvexHull2D(projected);
  if (hull.size() < 3) {
    if (fail_reason) *fail_reason = "2D convex hull has fewer than 3 vertices";
    return false;
  }
  std::set<int> hull_vertices(hull.begin(), hull.end());

  // 2. Build candidate hull contacts from true hull cycle
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

  // Also include standard silhouette contacts on hull vertices
  std::vector<ContactInfo> std_contacts = GenerateSilhouetteContacts(centroid, mixes);
  for (const auto &c : std_contacts) {
    if (hull_vertices.count(c.vertex)) {
      candidate_contacts.push_back(c);
    }
  }

  // Deduplicate candidate contacts
  auto ContactKey = [](const ContactInfo &c) {
    return std::make_tuple(c.vertex, c.edge_start, c.edge_finish, c.edge_start2, c.edge_finish2, c.mix);
  };
  std::sort(candidate_contacts.begin(), candidate_contacts.end(),
            [&](const ContactInfo &a, const ContactInfo &b) {
              return ContactKey(a) < ContactKey(b);
            });
  candidate_contacts.erase(
      std::unique(candidate_contacts.begin(), candidate_contacts.end(),
                  [&](const ContactInfo &a, const ContactInfo &b) {
                    return ContactKey(a) == ContactKey(b);
                  }),
      candidate_contacts.end());

  // 3. Filter contacts that have non-positive support defect across tri
  std::vector<ContactInfo> valid_contacts;
  for (const auto &c : candidate_contacts) {
    vec3 edge = GetDoubleEdge(c);
    int sel = c.vertex;
    bool ok = true;
    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta_v = Vertex(k) - Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta_v);
      double u0 = yocto::dot(tri_f[0], coeff);
      double u1 = yocto::dot(tri_f[1], coeff);
      double u2 = yocto::dot(tri_f[2], coeff);
      if (std::max({u0, u1, u2}) > 1e-12) {
        ok = false;
        break;
      }
    }
    if (ok) valid_contacts.push_back(c);
  }

  // 4. Search triples of valid contacts with positive 2D displacement
  for (size_t i = 0; i < valid_contacts.size(); i++) {
    for (size_t j = i + 1; j < valid_contacts.size(); j++) {
      for (size_t k = j + 1; k < valid_contacts.size(); k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        CandidateTriple cand;
        if (!DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        // Verify with exact rational audit
        AxisCertificate exact_cert;
        BigVecQ3 center;
        BigRat delta;
        std::string fail;
        if (AuditAxis(tri, triple, &exact_cert, &center, &delta, &fail)) {
          *out_cert = exact_cert;
          if (out_center) *out_center = center;
          if (out_delta) *out_delta = delta;
          return true;
        }
      }
    }
  }

  if (fail_reason) *fail_reason = "No valid 9-vertex hull contact triple found";
  return false;
}

std::vector<Tube229::AuditedAxis> Tube229::FindAllHullSupportAxes(
    const tubetree229::TriangleQ &tri,
    size_t max_axes) {
  std::vector<AuditedAxis> result;
  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  vec3 centroid = (c0 + c1 + c2) * (1.0 / 3.0);
  double vlen = yocto::length(centroid);
  if (vlen < 1e-12) return result;
  vec3 unit_view = centroid / vlen;

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

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> hull = ConvexHull2D(projected);
  if (hull.size() < 3) return result;
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

  std::vector<ContactInfo> std_contacts = GenerateSilhouetteContacts(centroid, mixes);
  for (const auto &c : std_contacts) {
    if (hull_vertices.count(c.vertex)) {
      candidate_contacts.push_back(c);
    }
  }

  auto ContactKey = [](const ContactInfo &c) {
    return std::make_tuple(c.vertex, c.edge_start, c.edge_finish, c.edge_start2, c.edge_finish2, c.mix);
  };
  std::sort(candidate_contacts.begin(), candidate_contacts.end(),
            [&](const ContactInfo &a, const ContactInfo &b) {
              return ContactKey(a) < ContactKey(b);
            });
  candidate_contacts.erase(
      std::unique(candidate_contacts.begin(), candidate_contacts.end(),
                  [&](const ContactInfo &a, const ContactInfo &b) {
                    return ContactKey(a) == ContactKey(b);
                  }),
      candidate_contacts.end());

  vec3 tri_f[3] = {c0, c1, c2};
  std::vector<ContactInfo> valid_contacts;
  for (const auto &c : candidate_contacts) {
    vec3 edge = GetDoubleEdge(c);
    int sel = c.vertex;
    bool ok = true;
    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (c.mix == 1000 && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta_v = Vertex(k) - Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta_v);
      double u0 = yocto::dot(tri_f[0], coeff);
      double u1 = yocto::dot(tri_f[1], coeff);
      double u2 = yocto::dot(tri_f[2], coeff);
      if (std::max({u0, u1, u2}) > 1e-12) {
        ok = false;
        break;
      }
    }
    if (ok) valid_contacts.push_back(c);
  }

  for (size_t i = 0; i < valid_contacts.size() && result.size() < max_axes; i++) {
    for (size_t j = i + 1; j < valid_contacts.size() && result.size() < max_axes; j++) {
      for (size_t k = j + 1; k < valid_contacts.size() && result.size() < max_axes; k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        CandidateTriple cand;
        if (!DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        AxisCertificate exact_cert;
        BigVecQ3 center;
        BigRat delta;
        std::string fail;
        if (AuditAxis(tri, triple, &exact_cert, &center, &delta, &fail)) {
          result.push_back({exact_cert, center, delta});
        }
      }
    }
  }
  return result;
}

bool Tube229::CheckAnnularDominance(
    const BigRat &B,
    const BigRat &defect_D,
    const BigRat &c_cone,
    const BigRat &delta,
    BigRat *in_out_r_min,
    BigRat *in_out_r) {
  if (B <= 0 || defect_D < 0 || c_cone <= delta) return false;

  // If radii are provided and positive, test them directly:
  if (in_out_r_min && in_out_r && *in_out_r_min > 0 && *in_out_r > *in_out_r_min) {
    const BigRat &r_min = *in_out_r_min;
    const BigRat &r = *in_out_r;

    BigRat r_sq = r * r;
    if (r_sq >= 4) return false;

    // LHS = ((1/2) * r^2 * B + D)^2
    BigRat inner_lhs = (BigRat(1, 2) * r_sq * B) + defect_D;
    BigRat lhs = inner_lhs * inner_lhs;

    // RHS = r_min^2 * (1 - (1/4) * r^2) * (c_cone - delta)^2 * B^2
    BigRat c_eff = c_cone - delta;
    BigRat factor1 = r_min * r_min;
    BigRat factor2 = BigRat(1) - (BigRat(1, 4) * r_sq);
    BigRat factor3 = (c_eff * c_eff) * (B * B);
    BigRat rhs = factor1 * factor2 * factor3;

    return (lhs <= rhs);
  }

  // Otherwise, automatically test conservative candidate radii
  BigRat candidate_r_min(1, 10000);
  BigRat candidate_r(1, 2000);

  BigRat r_sq = candidate_r * candidate_r;
  BigRat inner_lhs = (BigRat(1, 2) * r_sq * B) + defect_D;
  BigRat lhs = inner_lhs * inner_lhs;
  BigRat c_eff = c_cone - delta;
  BigRat rhs = (candidate_r_min * candidate_r_min) * (BigRat(1) - (BigRat(1, 4) * r_sq)) * ((c_eff * c_eff) * (B * B));

  if (lhs <= rhs) {
    if (in_out_r_min) *in_out_r_min = candidate_r_min;
    if (in_out_r) *in_out_r = candidate_r;
    return true;
  }

  // Finer search if needed
  double B_f = B.ToDouble();
  double D_f = defect_D.ToDouble();
  double c_eff_f = c_eff.ToDouble();
  double min_r_min = std::sqrt(2.0 * D_f / std::max(1e-12, c_eff_f * B_f));
  double r_min_f = min_r_min * 1.5;
  double r_f = std::min(0.01, std::sqrt(r_min_f));
  if (r_min_f >= r_f) r_min_f = r_f * 0.5;

  BigRat sol_r_min = CeilTo(BigRat::FromDouble(r_min_f), 1000000LL);
  BigRat sol_r = FloorTo(BigRat::FromDouble(r_f), 1000000LL);
  if (sol_r_min <= 0 || sol_r <= sol_r_min) return false;

  BigRat sol_r_sq = sol_r * sol_r;
  BigRat sol_lhs = ((BigRat(1, 2) * sol_r_sq * B) + defect_D);
  sol_lhs = sol_lhs * sol_lhs;
  BigRat sol_rhs = (sol_r_min * sol_r_min) * (BigRat(1) - (BigRat(1, 4) * sol_r_sq)) * ((c_eff * c_eff) * (B * B));

  if (sol_lhs <= sol_rhs) {
    if (in_out_r_min) *in_out_r_min = sol_r_min;
    if (in_out_r) *in_out_r = sol_r;
    return true;
  }

  return false;
}

bool Tube229::EvaluateComplementConeCoverage(
    const TriangleQ &tri,
    const std::vector<AxisCertificate> &axes,
    const vec3 &exceptional_axis_dir,
    double c_cone_thresh,
    BigRat *out_c_comp,
    int sphere_samples) {
  if (axes.empty()) return false;

  // 1. Audit that each candidate axis has support defect <= 0 over tri
  std::vector<vec3> axis_dirs;
  for (size_t a = 0; a < axes.size(); a++) {
    ContactInfo triple[3] = {axes[a].contacts[0], axes[a].contacts[1], axes[a].contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    if (!AuditAxis(tri, triple, &cert, &center, &delta, &fail)) {
      return false;
    }
    vec3 c_f = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
    double norm_c = yocto::length(c_f);
    if (norm_c < 1e-12) return false;
    axis_dirs.push_back(c_f / norm_c);
  }

  // 2. Dense Fibonacci sphere evaluation outside the exceptional cone
  vec3 exc_dir = yocto::normalize(exceptional_axis_dir);
  double min_cover = 1e30;
  int evaluated_points = 0;

  double golden_ratio = (1.0 + std::sqrt(5.0)) / 2.0;
  for (int i = 0; i < sphere_samples; i++) {
    double theta = 2.0 * M_PI * i / golden_ratio;
    double phi = std::acos(1.0 - 2.0 * (i + 0.5) / sphere_samples);
    vec3 omega = {std::cos(theta) * std::sin(phi), std::sin(theta) * std::sin(phi), std::cos(phi)};

    // Only test directions outside the exceptional cone: dot(omega, exc_dir) < c_cone_thresh
    double dot_exc = yocto::dot(omega, exc_dir);
    if (dot_exc >= c_cone_thresh) continue;

    evaluated_points++;
    double max_dot = -1e30;
    for (const auto &ad : axis_dirs) {
      double d = yocto::dot(omega, ad);
      if (d > max_dot) max_dot = d;
    }
    if (max_dot < min_cover) {
      min_cover = max_dot;
    }
  }

  if (evaluated_points == 0 || min_cover <= 0) return false;

  if (out_c_comp) {
    // Round down conservatively to 6 decimal places
    *out_c_comp = FloorTo(BigRat::FromDouble(min_cover), 1000000LL);
  }
  return true;
}

bool Tube229::SynthesizeDecomposedCertificate(
    const TriangleQ &tri,
    int depth,
    DecomposedCertificate *out_decomp,
    const TubeCertificate *sibling_cert,
    std::string *fail_reason) {
  // 1. Find the 9-vertex hull inner core axis
  AxisCertificate inner_core;
  BigVecQ3 inner_center;
  BigRat inner_delta;
  std::string hull_fail;
  if (!FindHullSupportAxis(tri, &inner_core, &inner_center, &inner_delta, &hull_fail)) {
    if (fail_reason) *fail_reason = "FindHullSupportAxis failed: " + hull_fail;
    return false;
  }

  out_decomp->inner_core_axis = inner_core;
  out_decomp->inner_index[0] = inner_core.contacts[0].vertex;
  out_decomp->inner_index[1] = inner_core.contacts[1].vertex;
  out_decomp->inner_index[2] = inner_core.contacts[2].vertex;

  // 2. Identify exceptional annular axis and complementary axes
  if (sibling_cert) {
    out_decomp->annular_axis = sibling_cert->axes[0];

    // Compute exact weights and defect D of annular axis across tri
    BigVecQ3 edges[3] = {
      GetExactEdge(out_decomp->annular_axis.contacts[0]),
      GetExactEdge(out_decomp->annular_axis.contacts[1]),
      GetExactEdge(out_decomp->annular_axis.contacts[2])
    };
    BigVecQ3 coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
    BigVecQ3 coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
    BigVecQ3 coeff2 = BigVecQ3::Cross(edges[0], edges[1]);
    BigVecQ3 w_coeffs[3] = {coeff0, coeff1, coeff2};

    BigRat w_upper[3];
    BigRat sum_w_upper(0);
    for (int m = 0; m < 3; m++) {
      BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
      for (int c = 1; c < 3; c++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
        if (val > w_max) w_max = val;
      }
      w_upper[m] = w_max;
      sum_w_upper = sum_w_upper + w_max;
    }
    out_decomp->annular_axis.B = sum_w_upper * BigRat(2);

    BigRat total_defect(0);
    for (int m = 0; m < 3; m++) {
      int sel = out_decomp->annular_axis.contacts[m].vertex;
      BigVecQ3 v_sel = VertexQ(sel);
      BigRat max_m_defect(0);
      for (int k = 0; k < NUM_VERTICES; k++) {
        bool tie = (k == sel) ||
                   (out_decomp->annular_axis.contacts[m].mix == 1000 && sel == out_decomp->annular_axis.contacts[m].edge_finish && k == out_decomp->annular_axis.contacts[m].edge_start) ||
                   (out_decomp->annular_axis.contacts[m].mix == 0 && sel == out_decomp->annular_axis.contacts[m].edge_start2 && k == out_decomp->annular_axis.contacts[m].edge_finish2);
        if (tie) continue;
        BigVecQ3 delta_v = VertexQ(k) - v_sel;
        BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta_v);
        BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
          if (val > max_s) max_s = val;
        }
        if (max_s > max_m_defect) max_m_defect = max_s;
      }
      total_defect = total_defect + max_m_defect * w_upper[m];
    }
    out_decomp->defect_D = total_defect;

    // Audit complementary axes directly on tri to obtain exact bounds and deltas
    std::vector<AxisCertificate> comp_axes(3);
    BigRat max_comp_delta(0);
    for (int a = 0; a < 3; a++) {
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      std::string fail;
      ContactInfo contacts[3] = {
        sibling_cert->axes[a + 1].contacts[0],
        sibling_cert->axes[a + 1].contacts[1],
        sibling_cert->axes[a + 1].contacts[2]
      };
      if (!AuditAxis(tri, contacts, &cert, &center, &delta, &fail)) {
        // Fall back to sibling cert if audit on tri failed
        cert = sibling_cert->axes[a + 1];
        delta = sibling_cert->delta;
      }
      comp_axes[a] = cert;
      if (delta > max_comp_delta) max_comp_delta = delta;
    }
    out_decomp->delta = max_comp_delta;

    // Compute exact direction of exceptional axis a_0 at centroid
    vec3 tri_f[3] = {ToDouble(tri.corners[0]), ToDouble(tri.corners[1]), ToDouble(tri.corners[2])};
    vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
    vec3 c_edges[3] = {GetDoubleEdge(out_decomp->annular_axis.contacts[0]),
                       GetDoubleEdge(out_decomp->annular_axis.contacts[1]),
                       GetDoubleEdge(out_decomp->annular_axis.contacts[2])};
    vec3 w_coeffs_d[3] = {yocto::cross(c_edges[1], c_edges[2]),
                          yocto::cross(c_edges[2], c_edges[0]),
                          yocto::cross(c_edges[0], c_edges[1])};
    vec3 weights = {yocto::dot(centroid, w_coeffs_d[0]),
                    yocto::dot(centroid, w_coeffs_d[1]),
                    yocto::dot(centroid, w_coeffs_d[2])};
    vec3 variation = {0, 0, 0};
    for (int m = 0; m < 3; m++) {
      vec3 lift = yocto::cross(centroid, c_edges[m]);
      vec3 term = yocto::cross(Vertex(out_decomp->annular_axis.contacts[m].vertex), lift);
      variation = variation + term * weights[m];
    }
    vec3 exc_dir = yocto::normalize(variation);

    // Search for optimal cone threshold where both annular dominance and
    // complementary coverage hold with positive margin
    BigRat best_c_comp(0);
    BigRat best_c_cone(0);
    BigRat best_r_min{0};
    BigRat best_r{0};

    for (double c_thresh : {0.30, 0.25, 0.20, 0.15, 0.10}) {
      BigRat rat_thresh = FloorTo(BigRat::FromDouble(c_thresh), 100LL);

      // Search candidate radii
      for (int r_denom : {2000, 1000, 500, 200}) {
        for (int r_min_denom : {20000, 10000, 5000, 2000, 1000}) {
          if (r_min_denom <= r_denom) continue;
          BigRat r_min(1, r_min_denom);
          BigRat r(1, r_denom);
          if (!CheckAnnularDominance(out_decomp->annular_axis.B, out_decomp->defect_D,
                                     rat_thresh, out_decomp->delta, &r_min, &r)) {
            continue;
          }
          BigRat c_comp;
          if (EvaluateComplementConeCoverage(tri, comp_axes, exc_dir, c_thresh, &c_comp, 20000) && c_comp > best_c_comp) {
            best_c_comp = c_comp;
            best_c_cone = rat_thresh;
            best_r_min = r_min;
            best_r = r;
          }
        }
      }
    }

    if (best_c_comp <= 0) {
      if (fail_reason) *fail_reason = "EvaluateComplementConeCoverage found no positive margin";
      return false;
    }

    out_decomp->c_cone = best_c_cone;
    out_decomp->c_comp = best_c_comp;
    out_decomp->r_min = best_r_min;
    out_decomp->r = best_r;
    out_decomp->complement_axes = comp_axes;
    out_decomp->symmetry_index = sibling_cert->symmetry_index;
    return true;
  }

  if (fail_reason) *fail_reason = "No sibling certificate provided for annular decomposition";
  return false;
}

