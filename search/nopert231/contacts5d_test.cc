#include "contacts5d.h"

#include <cmath>
#include <cstdio>
#include <random>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"
#include "geom5d.h"
#include "nopert231.h"
#include "rapidjson/document.h"
#include "util.h"

using namespace contacts5d;
using exact5d::Q;

static std::vector<exact5d::TriangleQ> CodeTriangles() {
  rapidjson::Document doc;
  doc.Parse(Util::ReadFile("codebdd231.json").c_str());
  CHECK(!doc.HasParseError());
  std::vector<exact5d::TriangleQ> out;
  for (const auto &code : doc["codes"].GetArray()) {
    for (const auto &t : code["triangles"].GetArray()) {
      exact5d::TriangleQ tri;
      for (int i = 0; i < 3; i++) {
        tri[i] = {Q(std::string_view(t[i]["x"].GetString())), Q(std::string_view(t[i]["y"].GetString())),
                  Q(std::string_view(t[i]["z"].GetString()))};
      }
      out.push_back(tri);
    }
  }
  return out;
}

static void TestEdges() {
  const auto &edges = PolyhedronEdges();
  // Euler: 20 vertices, 27 faces -> 45 edges.
  CHECK((int)edges.size() == NUM_VERTICES + 27 - 2) << edges.size();
  std::vector<int> degree(NUM_VERTICES, 0);
  for (const auto &[a, b] : edges) {
    CHECK(a < b);
    degree[a]++;
    degree[b]++;
  }
  for (int d : degree) CHECK(d >= 3);
  printf("  %d polyhedron edges OK\n", (int)edges.size());
}

static void TestPools() {
  const auto tris = CodeTriangles();
  std::mt19937_64 rng(5);
  int pools = 0, triples_checked = 0;
  for (int n = 0; n < 12; n++) {
    exact5d::TriangleQ tq = tris[rng() % tris.size()];
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
  TestPools();
  printf("contacts5d tests PASSED\n");
  return 0;
}
