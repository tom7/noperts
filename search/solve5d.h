// Solving 5D search nodes. A job is a code triangle t and a chart (0..2;
// chart 3 is a fixed table in Lean). A node, named by its split path
// (rows5d), is closed by the cheapest applicable leaf, else split:
//
//   pr  the box lies outside the Cayley ball
//   pf  the box lies outside the fivefold fundamental domain
//   tu  chart 0, and the box lies in the identity tube of the radius the tube
//       table certifies at this view (tubeatlas5d)
//   ce  a single contact triple certifies the node (cert5d) with a positive
//       (conservative) double margin; optionally confirmed by exact5d
//
// Prunes and tubes are decided with the exact predicates Lean uses (exact5d);
// certificates are confirmed exactly at packing time (and by Lean).

#ifndef _NOPERT229_SOLVE5D_H
#define _NOPERT229_SOLVE5D_H

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "cert5d.h"
#include "contacts5d.h"
#include "exact5d.h"
#include "geom5d.h"
#include "rows5d.h"
#include "tubeatlas5d.h"

namespace solve5d {

struct Options {
  int cone_samples = 8;
  // Triples fully evaluated per node after center screening.
  int max_full = 64;
  // Split the box when its widest half-width exceeds split_kappa times the
  // view triangle's angular diameter, else split the view.
  double split_kappa = 0.5;
  // Nodes deeper than this become deferred (df) leaves.
  int max_depth = 80;
  // Confirm every certificate leaf with exact5d before accepting it. Off by
  // default: it costs ~30x the double search (the code triangles' corners are
  // ~1000-bit rationals), the double margin is conservative (no exact
  // rejections seen), and packing and Lean check every leaf anyway.
  bool exact_check = false;
};

struct Job {
  int t = 0;      // code triangle (WedgeCover.codeTriangles index)
  int chart = 0;  // 0..2
};

struct Node {
  std::string path;
  exact5d::TriangleQ tri;
  geom5d::BoxQ box;
};

Node RootNode(const tubeatlas5d::TubeAtlas &atlas, const Job &job);
std::vector<Node> Children(const Node &node, char split);

struct Stats {
  int64_t nodes = 0;
  int64_t ce = 0, tu = 0, pr = 0, pf = 0, df = 0;
  // Certificates whose double margin was positive but which the exact check
  // rejected (a sign the double screen is too optimistic).
  int64_t exact_rejects = 0;
  double worst_margin = 1e300;
  int64_t max_pool_triples = 0;
  void Add(const Stats &o);
};

class Solver {
 public:
  Solver(const tubeatlas5d::TubeAtlas *atlas, const Job &job, const Options &opt)
      : atlas_(atlas), job_(job), opt_(opt) {}

  // The cheap leaves only (pr, pf, tu); no certificate search.
  std::optional<rows5d::Leaf> TryPrune(const Node &node) const;
  // Any leaf (prunes first, then a certificate).
  std::optional<rows5d::Leaf> TryLeaf(const Node &node);
  // 'v' for a view split, or the box step's axis as 'x', 'y', 'z'.
  char ChooseSplit(const Node &node) const;

  // Solves the subtree at `root` depth first. After `max_nodes` nodes (or
  // past opt.max_depth), unexplored nodes become deferred leaves, so the
  // result is always a complete tree.
  std::vector<rows5d::Record> SolveSubtree(const Node &root, int64_t max_nodes);

  const Stats &stats() const { return stats_; }

 private:
  const contacts5d::ContactPool &Pool(const Node &node);

  const tubeatlas5d::TubeAtlas *atlas_;
  Job job_;
  Options opt_;
  Stats stats_;
  // Pools of the most recently used views (the depth-first search revisits a
  // view across consecutive box splits). Pools can be large (up to ~C(256,3)
  // triples), so only a few are kept.
  static constexpr size_t kMaxCachedPools = 4;
  std::vector<std::pair<std::string, std::unique_ptr<contacts5d::ContactPool>>> pools_;
};

}  // namespace solve5d

#endif
