#include "solve5d.h"

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <string>
#include <variant>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "rows5d.h"
#include "tubeatlas5d.h"

using namespace solve5d;

// Re-checks every leaf of a solved subtree exactly, independently of the
// solver, and that the leaves form a complete tree.
static void VerifySubtree(const tubeatlas5d::TubeAtlas &atlas, const Job &job,
                          const Node &root, const std::vector<rows5d::Record> &leaves,
                          const Options &opt) {
  auto tree = rows5d::BuildTree(leaves, root.path);
  CHECK(std::holds_alternative<rows5d::Tree>(tree)) << std::get<std::string>(tree);
  const Node job_root = RootNode(atlas, job);
  for (const auto &r : leaves) {
    const auto tri = rows5d::NodeTriangle(job_root.tri, r.path);
    const auto box = rows5d::NodeBox(job_root.box, r.path);
    const auto iv = geom5d::ToInterval(box);
    std::visit(
        [&](const auto &l) {
          using T = std::decay_t<decltype(l)>;
          if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) {
            CHECK(exact5d::OutsideCayleyBall(iv));
          } else if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) {
            CHECK(exact5d::FundamentalPruneValid(iv, job.chart, l.direction));
          } else if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) {
            CHECK(job.chart == 0);
            CHECK(exact5d::IdentityTubeValid(iv, l.r));
            CHECK(l.r == atlas.Walk(job.t, rows5d::ViewPath(r.path)).r_lower);
          } else if constexpr (std::is_same_v<T, rows5d::MixedLeaf>) {
            contacts5d::PoolParams params;
            params.cone_samples = l.cone_samples;
            const auto pool = contacts5d::BuildContactPool(geom5d::ToDouble(tri), params);
            std::vector<int> triples;
            std::vector<std::array<int, 3>> inner;
            std::vector<BigRat> weights;
            for (const auto &c : l.components) {
              triples.push_back(c.triple);
              inner.push_back(c.inner);
              weights.push_back(c.weight);
            }
            CHECK(exact5d::Valid(cert5d::ExactMixedBox(pool, triples, inner, weights, tri, box, job.chart)))
                << "mixture leaf " << r.path;
          } else if constexpr (std::is_same_v<T, rows5d::CertLeaf>) {
            contacts5d::PoolParams params;
            params.cone_samples = l.cone_samples;
            const auto pool = contacts5d::BuildContactPool(geom5d::ToDouble(tri), params);
            CHECK(l.triple < (int)pool.triples.size());
            const cert5d::Single s{.triple = l.triple, .inner = l.inner};
            CHECK(exact5d::Valid(cert5d::ExactGlobalBox(pool, s, tri, box, job.chart)))
                << "certificate leaf " << r.path;
          }
        },
        r.leaf);
  }
}

// Test data, not committed: refined identity-tube trees (rebuild.sh's
// trees_r2) in $TREES_DIR (default trees_r2), and codebdd's output in
// $CODEBDD_JSON (default codebdd.json). Without them the test is skipped.
static std::string EnvOr(const char *name, const char *dflt) {
  const char *e = getenv(name);
  return e != nullptr ? e : dflt;
}

int main() {
  const std::string trees = EnvOr("TREES_DIR", "trees_r2");
  const std::string bdd = EnvOr("CODEBDD_JSON", "codebdd.json");
  if (!std::filesystem::exists(trees + "/tree.0.json") || !std::filesystem::exists(bdd)) {
    printf("SKIPPED: %s/tree.0.json or %s not present\n", trees.c_str(), bdd.c_str());
    return 0;
  }
  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees, bdd);
  Options opt;
  // The search screens in double; VerifySubtree checks every leaf exactly.
  // A few subtrees in different charts, a few levels down from the root.
  struct Case {
    Job job;
    int descend;
    bool toward_origin;  // follow the child nearest the box origin
  };
  for (const Case &c : {Case{{0, 1}, 9, false}, Case{{40, 2}, 9, false}, Case{{100, 0}, 9, false},
                        Case{{0, 1}, 3, false}, Case{{70, 0}, 6, true}}) {
    Solver solver(&atlas, c.job, opt);
    Node node = RootNode(atlas, c.job);
    for (int d = 0; d < c.descend; d++) {
      if (solver.TryPrune(node)) break;
      auto ch = Children(node, solver.ChooseSplit(node));
      node = c.toward_origin ? ch.front() : ch.back();
      if (c.toward_origin && ch.size() == 2) {
        // The half whose box is nearer the origin.
        const auto lo = geom5d::ToDouble(ch[0].box), hi = geom5d::ToDouble(ch[1].box);
        node = yocto::length(lo.center) <= yocto::length(hi.center) ? ch[0] : ch[1];
      }
    }
    const auto start = std::chrono::steady_clock::now();
    const auto leaves = solver.SolveSubtree(node, 3000);
    const double sec =
        std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    const Stats &s = solver.stats();
    printf("  t=%d chart=%d root '%s': %lld nodes in %.1fs: ce %lld mx %lld tu %lld pr %lld pf %lld df %lld "
           "(exact rejects %lld)\n",
           c.job.t, c.job.chart, node.path.c_str(), (long long)s.nodes, sec, (long long)s.ce, (long long)s.mx,
           (long long)s.tu, (long long)s.pr, (long long)s.pf, (long long)s.df,
           (long long)s.exact_rejects);
    VerifySubtree(atlas, c.job, node, leaves, opt);
  }
  printf("solve5d tests PASSED\n");
  return 0;
}
