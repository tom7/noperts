#include "contacts5d.h"

#include <algorithm>
#include <cmath>
#include <unordered_set>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "geom/hull-2d.h"
#include "model.h"

namespace contacts5d {

using vec2 = yocto::vec<double, 2>;

namespace {

vec3 V(int k) { return Vertex(k); }

// The double edge direction of a contact, from its integer description.
vec3 ContactEdge(int es, int ef, int es2, int ef2, int mix) {
  const double lam = mix / 1000.0;
  return lam * (V(es) - V(ef)) + (1.0 - lam) * (V(es2) - V(ef2));
}

// Max (over vertices k != vertex) of the max over the triangle's corners of
// the support excess of k past the contact's support line; also returns the
// min over k of those per-vertex maxima.
std::pair<double, double> SupportExcess(const geom5d::TriangleD &tri, int vertex,
                                        const vec3 &e) {
  double max_upper = 0.0, min_upper = 1e30;
  for (int k = 0; k < NUM_VERTICES; k++) {
    if (k == vertex) continue;
    const vec3 coeff = yocto::cross(e, V(k) - V(vertex));
    if (yocto::length(coeff) < 1e-12) continue;
    const double upper = std::max({yocto::dot(tri.corners[0], coeff),
                                   yocto::dot(tri.corners[1], coeff),
                                   yocto::dot(tri.corners[2], coeff)});
    max_upper = std::max(max_upper, upper);
    min_upper = std::min(min_upper, upper);
  }
  return {max_upper, min_upper};
}

// Adds contacts at `vertex` with edge directions interpolating
// (prev - vertex) and (vertex - next). Returns false once the pool is full.
bool AddCornerContacts(const geom5d::TriangleD &tri, const PoolParams &params, int prev,
                       int vertex, int next, double max_defect,
                       std::vector<Contact> *contacts) {
  for (int s = 0; s <= params.cone_samples + 1; s++) {
    const int mix = (int)std::lround(1000.0 * s / (params.cone_samples + 1.0));
    const vec3 e = ContactEdge(prev, vertex, vertex, next, mix);
    const auto [max_upper, min_upper] = SupportExcess(tri, vertex, e);
    // Some vertex must be strictly behind the support line, and the
    // worst excess must be small enough.
    if (min_upper >= 0.0 || max_upper > max_defect) continue;
    const vec3 e_norm = yocto::normalize(e);
    bool duplicate = false;
    for (const Contact &ex : *contacts) {
      if (yocto::dot(e_norm, yocto::normalize(ex.edge)) > 1.0 - 1e-9) {
        duplicate = true;
        break;
      }
    }
    if (duplicate) continue;
    if ((int)contacts->size() >= params.max_contacts) return false;
    contacts->push_back(Contact{.vertex = vertex, .edge_start = prev, .edge_finish = vertex,
                                .edge_start2 = vertex, .edge_finish2 = next, .mix = mix,
                                .edge = e, .defect = std::max(0.0, max_upper)});
  }
  return true;
}

// Adds bridge contacts across a short silhouette edge (vertex, next): at
// `vertex` and at `next`, edge directions interpolating (prev - vertex) and
// (next - next2), skipping the short edge, whose direction turns quickly with
// the view (e.g. near a view along that polyhedron edge, where its endpoints
// coincide in projection). The support defect of the other endpoint is
// small (about the edge's projected length). Lean's AxisCertificate takes
// any two edges and any support vertex.
bool AddBridgeContacts(const geom5d::TriangleD &tri, const PoolParams &params, int prev,
                       int vertex, int next, int next2, std::vector<Contact> *contacts) {
  for (int at : {vertex, next}) {
    for (int s = 0; s <= params.cone_samples + 1; s++) {
      const int mix = (int)std::lround(1000.0 * s / (params.cone_samples + 1.0));
      const vec3 e = ContactEdge(prev, vertex, next, next2, mix);
      const auto [max_upper, min_upper] = SupportExcess(tri, at, e);
      if (min_upper >= 0.0 || max_upper > params.bridge_max_defect) continue;
      const vec3 e_norm = yocto::normalize(e);
      bool duplicate = false;
      for (const Contact &ex : *contacts) {
        if (ex.vertex == at && yocto::dot(e_norm, yocto::normalize(ex.edge)) > 1.0 - 1e-9) {
          duplicate = true;
          break;
        }
      }
      if (duplicate) continue;
      if ((int)contacts->size() >= params.max_contacts) return false;
      contacts->push_back(Contact{.vertex = at, .edge_start = prev, .edge_finish = vertex,
                                  .edge_start2 = next, .edge_finish2 = next2, .mix = mix,
                                  .edge = e, .defect = std::max(0.0, max_upper)});
    }
  }
  return true;
}

// Double-precision version of Lean's Box.weightedDefectUpper for one triple,
// with a margin (1e-9 added to each affine factor; Lean adds 6e-15).
//
// For contact i the bound is max(0, max over vertices k and corner pairs (a, b)
// of (w_a s_kb + w_b s_ka) / 2), where s_k depends only on the contact and the
// weights w_a > 0 on the triple. With positive weights the maximum over k is
// attained on the Pareto frontier of the points (s_kb, s_ka), so each
// contact's frontiers are computed once per pool (DefectFrontiers) and the
// value is the same as the direct maximum over all vertices.
constexpr double kDefectError = 1e-9;

struct DefectFrontiers {
  // Pairs (0,0), (1,1), (2,2): the maximum s_ka; pairs (0,1), (0,2), (1,2): the
  // staircase of points (s_kb, s_ka) not dominated in both coordinates.
  double diag[3];
  std::vector<std::pair<double, double>> off[3];
};

DefectFrontiers MakeDefectFrontiers(const geom5d::TriangleD &tri, const Contact &ct) {
  DefectFrontiers f;
  std::vector<std::array<double, 3>> S;
  for (int k = 0; k < NUM_VERTICES; k++) {
    if (k == ct.vertex) continue;
    const vec3 s_coeff = yocto::cross(ct.edge, V(k) - V(ct.vertex));
    std::array<double, 3> s;
    for (int a = 0; a < 3; a++) s[a] = yocto::dot(tri.corners[a], s_coeff) + kDefectError;
    S.push_back(s);
  }
  for (int a = 0; a < 3; a++) {
    f.diag[a] = -1e300;
    for (const auto &s : S) f.diag[a] = std::max(f.diag[a], s[a]);
  }
  static constexpr int kPairs[3][2] = {{0, 1}, {0, 2}, {1, 2}};
  for (int p = 0; p < 3; p++) {
    const int a = kPairs[p][0], b = kPairs[p][1];
    std::vector<std::pair<double, double>> pts;
    for (const auto &s : S) pts.push_back({s[b], s[a]});
    std::sort(pts.begin(), pts.end(), [](auto &x, auto &y) { return x.first > y.first || (x.first == y.first && x.second > y.second); });
    double best_y = -1e300;
    for (const auto &q : pts) {
      if (q.second > best_y) { f.off[p].push_back(q); best_y = q.second; }
    }
  }
  return f;
}

double WeightedDefectUpper(const geom5d::TriangleD &tri, const std::vector<DefectFrontiers> &fr,
                           const std::array<int, 3> &c, const std::array<vec3, 3> &w_coeff) {
  static constexpr int kPairs[3][2] = {{0, 1}, {0, 2}, {1, 2}};
  double total = 0.0;
  for (int i = 0; i < 3; i++) {
    const DefectFrontiers &f = fr[c[i]];
    double w[3];
    for (int a = 0; a < 3; a++) w[a] = yocto::dot(tri.corners[a], w_coeff[i]) + kDefectError;
    double upper = 0.0;
    for (int a = 0; a < 3; a++) upper = std::max(upper, w[a] * f.diag[a]);
    for (int p = 0; p < 3; p++) {
      const double wa = w[kPairs[p][0]], wb = w[kPairs[p][1]];
      for (const auto &[sb, sa] : f.off[p]) upper = std::max(upper, 0.5 * (wa * sb + wb * sa));
    }
    total += upper;
  }
  return total;
}

}  // namespace

const std::vector<std::pair<int, int>> &PolyhedronEdges() {
  static const std::vector<std::pair<int, int>> *edges = [] {
    // Facet planes: triples (a, b, c) with all vertices on one side
    // (exactly), deduplicated by the set of vertices on the plane. A
    // floating-point pass first discards triples with vertices clearly on
    // both sides (model coordinates can have hundreds of bits).
    std::vector<std::vector<int>> facets;
    for (int a = 0; a < NUM_VERTICES; a++) {
      for (int b = a + 1; b < NUM_VERTICES; b++) {
        for (int c = b + 1; c < NUM_VERTICES; c++) {
          const vec3 nd = yocto::cross(V(b) - V(a), V(c) - V(a));
          const double scale = yocto::length(nd);
          if (scale > 1e-6) {
            bool pos = false, neg = false;
            for (int k = 0; k < NUM_VERTICES && !(pos && neg); k++) {
              const double s = yocto::dot(nd, V(k) - V(a)) / scale;
              if (s > 1e-9) pos = true;
              else if (s < -1e-9) neg = true;
            }
            if (pos && neg) continue;
          }
          const BigVecQ3 n = BigVecQ3::Cross(VertexQ(b) - VertexQ(a), VertexQ(c) - VertexQ(a));
          if (n.x == BigRat(0) && n.y == BigRat(0) && n.z == BigRat(0)) continue;
          const BigRat d = BigVecQ3::Dot(n, VertexQ(a));
          bool pos = false, neg = false;
          std::vector<int> on;
          for (int k = 0; k < NUM_VERTICES; k++) {
            const BigRat s = BigVecQ3::Dot(n, VertexQ(k)) - d;
            if (s > BigRat(0)) pos = true;
            else if (s < BigRat(0)) neg = true;
            else on.push_back(k);
          }
          if (pos && neg) continue;
          if (std::find(facets.begin(), facets.end(), on) == facets.end()) facets.push_back(on);
        }
      }
    }
    auto *out = new std::vector<std::pair<int, int>>;
    for (int i = 0; i < NUM_VERTICES; i++) {
      for (int j = i + 1; j < NUM_VERTICES; j++) {
        int shared = 0;
        for (const auto &f : facets) {
          if (std::find(f.begin(), f.end(), i) != f.end() &&
              std::find(f.begin(), f.end(), j) != f.end()) {
            shared++;
          }
        }
        // Two copies of one point (a vertex listed in several slots) are not an edge.
        if (shared >= 2 && !(VertexQ(i) == VertexQ(j))) out->push_back({i, j});
      }
    }
    return out;
  }();
  return *edges;
}

std::vector<int> SilhouetteCycle(const vec3 &view) {
  const vec3 uview = yocto::normalize(view);
  int min_axis = 0;
  for (int a = 1; a < 3; a++) {
    if (std::abs(uview[a]) < std::abs(uview[min_axis])) min_axis = a;
  }
  vec3 axis = {0, 0, 0};
  axis[min_axis] = 1.0;
  const vec3 right = yocto::normalize(yocto::cross(uview, axis));
  const vec3 up = yocto::cross(uview, right);
  std::vector<vec2> projected(NUM_VERTICES);
  for (int i = 0; i < NUM_VERTICES; i++) {
    projected[i] = {yocto::dot(V(i), right), yocto::dot(V(i), up)};
  }
  return Hull2D::GrahamScan(projected);
}

ContactPool BuildContactPool(const geom5d::TriangleD &tri, const PoolParams &params) {
  ContactPool pool;
  pool.params = params;
  const vec3 view = geom5d::Centroid(tri);
  if (yocto::length(view) < 1e-12) return pool;

  // Silhouette contacts at each hull corner, between its two hull edges.
  const std::vector<int> hull = SilhouetteCycle(view);
  const int H = hull.size();
  if (H < 3) return pool;
  std::vector<Contact> &contacts = pool.contacts;
  bool room = true;
  for (int i = 0; i < H && room; i++) {
    room = AddCornerContacts(tri, params, hull[(i - 1 + H) % H], hull[i], hull[(i + 1) % H],
                             1e30, &contacts);
  }

  // Bridge contacts across short silhouette edges (projected length below
  // bridge_ratio times the longest).
  if (params.bridge_ratio > 0 && H >= 4) {
    const vec3 uview = yocto::normalize(view);
    auto proj_len = [&](int a, int b) {
      const vec3 d = V(a) - V(b);
      return yocto::length(d - uview * yocto::dot(d, uview));
    };
    double longest = 0;
    for (int i = 0; i < H; i++) longest = std::max(longest, proj_len(hull[i], hull[(i + 1) % H]));
    for (int i = 0; i < H && room; i++) {
      const int v = hull[i], n = hull[(i + 1) % H];
      if (proj_len(v, n) >= params.bridge_ratio * longest) continue;
      room = AddBridgeContacts(tri, params, hull[(i - 1 + H) % H], v, n, hull[(i + 2) % H], &contacts);
    }
  }

  // Off-silhouette contacts at the other vertices, between any two of
  // their polyhedron edges, if their defect is small.
  std::vector<std::vector<int>> adj(NUM_VERTICES);
  for (const auto &[a, b] : PolyhedronEdges()) {
    adj[a].push_back(b);
    adj[b].push_back(a);
  }
  const std::unordered_set<int> hull_set(hull.begin(), hull.end());
  for (int v = 0; v < NUM_VERTICES && room; v++) {
    if (hull_set.count(v)) continue;
    for (int p : adj[v]) {
      for (int n : adj[v]) {
        if (p == n || !room) continue;
        room = AddCornerContacts(tri, params, p, v, n, params.off_silhouette_max_defect,
                                 &contacts);
      }
    }
  }

  // Triples whose three contact weights are positive over the triangle.
  const int C = contacts.size();
  std::vector<DefectFrontiers> frontiers;
  frontiers.reserve(C);
  for (const Contact &ct : contacts) frontiers.push_back(MakeDefectFrontiers(tri, ct));
  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        std::array<int, 3> c = {i, j, k};
        auto coeffs = [&]() -> std::array<vec3, 3> {
          const vec3 &e0 = contacts[c[0]].edge, &e1 = contacts[c[1]].edge, &e2 = contacts[c[2]].edge;
          return {yocto::cross(e1, e2), yocto::cross(e2, e0), yocto::cross(e0, e1)};
        };
        std::array<vec3, 3> w = coeffs();
        if (yocto::dot(view, w[0]) < 0 && yocto::dot(view, w[1]) < 0 &&
            yocto::dot(view, w[2]) < 0) {
          std::swap(c[1], c[2]);
          w = coeffs();
        }
        bool ok = true;
        for (int m = 0; m < 3 && ok; m++) {
          if (yocto::dot(view, w[m]) <= 1e-9) ok = false;
          // Strictly positive at every corner, with headroom far above Lean's
          // supportError (6e-15) so that the exact weightLower is positive.
          for (int a = 0; a < 3 && ok; a++) {
            if (yocto::dot(tri.corners[a], w[m]) <= 1e-11) ok = false;
          }
        }
        if (!ok) continue;
        pool.triples.push_back(Triple{.c = c,
                                      .weighted_defect_upper = WeightedDefectUpper(tri, frontiers, c, w)});
      }
    }
  }
  return pool;
}

exact5d::AxisCertificate ToAxisCertificate(const ContactPool &pool, const Triple &triple,
                                           const exact5d::TriangleQ &tri) {
  exact5d::AxisCertificate cert;
  for (int m = 0; m < 3; m++) {
    const Contact &ct = pool.contacts[triple.c[m]];
    cert.edge_start[m] = ct.edge_start;
    cert.edge_finish[m] = ct.edge_finish;
    cert.edge_start2[m] = ct.edge_start2;
    cert.edge_finish2[m] = ct.edge_finish2;
    cert.mix[m] = ct.mix;
    cert.index[m] = ct.vertex;
  }
  cert.B = exact5d::Q(1);
  exact5d::GlobalBox probe;
  probe.triangle = tri;
  probe.certificate = cert;
  const auto support = exact5d::SupportUppers(probe);
  for (int m = 0; m < 3; m++) {
    int best = 0;
    for (int k = 1; k < NUM_VERTICES; k++) {
      if (support[m][k] < support[m][best]) best = k;
    }
    cert.nonzero_witness[m] = best;
  }
  return cert;
}

}  // namespace contacts5d
