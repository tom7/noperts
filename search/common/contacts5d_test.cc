#include "contacts5d.h"

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <random>
#include <set>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"
#include "geom5d.h"
#include "model.h"
#include "rapidjson/document.h"
#include "test-data.h"
#include "util.h"

using namespace contacts5d;
using exact5d::Q;

static std::vector<exact5d::TriangleQ> CodeTriangles(std::vector<int> *roots) {
  rapidjson::Document doc;
  doc.Parse(Util::ReadFile(CodebddJson()).c_str());
  CHECK(!doc.HasParseError());
  std::vector<exact5d::TriangleQ> out;
  for (const auto &code : doc["codes"].GetArray()) {
    const int root = code.HasMember("root") ? code["root"].GetInt() : 0;
    for (const auto &t : code["triangles"].GetArray()) {
      exact5d::TriangleQ tri;
      for (int i = 0; i < 3; i++) {
        tri[i] = {Q(std::string_view(t[i]["x"].GetString())), Q(std::string_view(t[i]["y"].GetString())),
                  Q(std::string_view(t[i]["z"].GetString()))};
      }
      out.push_back(tri);
      roots->push_back(root);
    }
  }
  return out;
}

// The facets of the hull of the (double) vertices, each as its sorted
// vertex set: the vertex sets of supporting planes through three vertices.
static std::set<std::vector<int>> HullFacets() {
  std::set<std::vector<int>> facets;
  for (int i = 0; i < NUM_VERTICES; i++) {
    for (int j = i + 1; j < NUM_VERTICES; j++) {
      for (int k = j + 1; k < NUM_VERTICES; k++) {
        const vec3 a = Vertex(i), b = Vertex(j), c = Vertex(k);
        const vec3 n = yocto::cross(b - a, c - a);
        const double len = yocto::length(n);
        if (len < 1e-9) continue;
        const double eps = 1e-9 * len;
        bool pos = false, neg = false;
        std::vector<int> on;
        for (int v = 0; v < NUM_VERTICES; v++) {
          const double d = yocto::dot(n, Vertex(v) - a);
          if (d > eps) pos = true;
          else if (d < -eps) neg = true;
          else on.push_back(v);
        }
        if (!(pos && neg)) facets.insert(on);
      }
    }
  }
  return facets;
}

static void TestEdges() {
  const auto &edges = PolyhedronEdges();
  // A point may be listed in several slots (a vertex on the C5 axis is listed
  // once per orbit). Compare by points: each slot's representative is the
  // first slot holding the same point.
  std::vector<int> rep(NUM_VERTICES);
  for (int v = 0; v < NUM_VERTICES; v++) {
    rep[v] = v;
    for (int u = 0; u < v; u++) {
      if (VertexQ(u) == VertexQ(v)) { rep[v] = u; break; }
    }
  }
  std::set<std::vector<int>> facets;
  for (const auto &f : HullFacets()) {
    std::set<int> r;
    for (int v : f) r.insert(rep[v]);
    facets.insert(std::vector<int>(r.begin(), r.end()));
  }
  std::set<std::pair<int, int>> point_edges;
  for (const auto &[a, b] : edges) {
    CHECK(a < b);
    CHECK(rep[a] != rep[b]) << a << "-" << b << " joins two copies of one point";
    point_edges.insert({std::min(rep[a], rep[b]), std::max(rep[a], rep[b])});
  }
  // Every slot's edges are its representative's.
  for (const auto &[a, b] : edges) {
    for (int c = 0; c < NUM_VERTICES; c++) {
      if (rep[c] != rep[a] || c == a) continue;
      CHECK(std::find(edges.begin(), edges.end(), std::make_pair(std::min(c, b), std::max(c, b))) !=
            edges.end()) << "copy " << c << " of " << a << " lacks the edge to " << b;
    }
  }
  int points = 0;
  for (int v = 0; v < NUM_VERTICES; v++) points += rep[v] == v;
  // The edge list may also triangulate a facet (the deltoidal
  // hexecontahedron's lists the kites' diagonals): an edge lies on two
  // facets (a hull edge) or inside one (a diagonal).
  std::vector<int> degree(NUM_VERTICES, 0);
  int hull_edges = 0, diagonals = 0;
  for (const auto &[a, b] : point_edges) {
    degree[a]++;
    degree[b]++;
    int on = 0;
    for (const auto &f : facets) {
      if (std::binary_search(f.begin(), f.end(), a) && std::binary_search(f.begin(), f.end(), b)) on++;
    }
    CHECK(on == 1 || on == 2) << a << "-" << b << " on " << on << " facets";
    (on == 2 ? hull_edges : diagonals)++;
  }
  // Euler's formula for the convex polyhedron.
  CHECK(hull_edges == points + (int)facets.size() - 2)
      << hull_edges << " hull edges, " << points << " points, " << facets.size() << " facets";
  for (int v = 0; v < NUM_VERTICES; v++) {
    if (rep[v] == v) CHECK(degree[v] >= 3);
  }
  // A facet with k vertices has k hull edges, plus its diagonals.
  int facet_diagonals = 0;
  for (const auto &f : facets) {
    int fe = 0;
    for (const auto &[a, b] : point_edges) {
      if (std::binary_search(f.begin(), f.end(), a) && std::binary_search(f.begin(), f.end(), b)) fe++;
    }
    CHECK(fe >= (int)f.size()) << fe << " edges on a facet with " << f.size() << " vertices";
    facet_diagonals += fe - (int)f.size();
  }
  CHECK(facet_diagonals == diagonals) << facet_diagonals << " vs " << diagonals;
  printf("  %d polyhedron edges (%d between distinct points: %d hull edges, %d diagonals), "
         "%d points, %d facets OK\n",
         (int)edges.size(), (int)point_edges.size(), hull_edges, diagonals, points,
         (int)facets.size());
}

static void TestPools() {
  std::vector<int> roots;
  const auto tris = CodeTriangles(&roots);
  std::mt19937_64 rng(5);
  int pools = 0, triples_checked = 0;
  for (int n = 0; n < 12; n++) {
    const size_t ti = rng() % tris.size();
    exact5d::TriangleQ tq = tris[ti];
    std::string path;
    const int depth = rng() % 8;
    for (int d = 0; d < depth; d++) path += (char)('0' + rng() % 4);
    tq = geom5d::SplitTrianglePath(tq, path);
    const geom5d::TriangleD td = geom5d::ToDouble(tq);
    PoolParams params;
    params.cone_samples = 4 + rng() % 9;
    const ContactPool pool = BuildContactPool(td, params);
    CHECK(!pool.contacts.empty());
    pools++;

    // Deterministic.
    const ContactPool again = BuildContactPool(td, params);
    CHECK(again.contacts.size() == pool.contacts.size() && again.triples.size() == pool.triples.size());
    for (size_t t = 0; t < pool.triples.size(); t++) CHECK(again.triples[t].c == pool.triples[t].c);

    // Double edges are the exact contact edges.
    for (const Contact &ct : pool.contacts) {
      exact5d::AxisCertificate one;
      one.edge_start[0] = ct.edge_start;
      one.edge_finish[0] = ct.edge_finish;
      one.edge_start2[0] = ct.edge_start2;
      one.edge_finish2[0] = ct.edge_finish2;
      one.mix[0] = ct.mix;
      const exact5d::VecQ e = exact5d::EdgeQ(one, 0);
      for (int k = 0; k < 3; k++) CHECK(std::abs(e[k].ToDouble() - ct.edge[k]) < 1e-14);
    }

    // Every triple (or a sample) is an exactly admissible Lean certificate
    // on this triangle, and its double defect bound is conservative.
    const int step = std::max<int>(1, pool.triples.size() / 40);
    for (size_t t = 0; t < pool.triples.size(); t += step) {
      const Triple &tr = pool.triples[t];
      exact5d::GlobalBox box;
      box.interval = geom5d::ToInterval(geom5d::RootBox(0));
      box.triangle = tq;
      box.root = roots[ti];
      box.certificate = ToAxisCertificate(pool, tr, tq);
      box.inner_index = box.certificate.index;
      CHECK(exact5d::Admissible(box)) << "pool " << n << " triple " << t;
      const double exact_defect = exact5d::WeightedDefectUpper(box).ToDouble();
      CHECK(tr.weighted_defect_upper >= exact_defect)
          << tr.weighted_defect_upper << " < " << exact_defect;
      triples_checked++;
    }
  }
  printf("  %d pools, %d triples exactly admissible with conservative defect bounds OK\n",
         pools, triples_checked);
}

int main() {
  TestEdges();
  if (HaveCodebddJson("the contact pools")) TestPools();
  printf("contacts5d tests PASSED\n");
  return 0;
}
