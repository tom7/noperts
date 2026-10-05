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
//   mx  else a mixture of up to four triples does
//
// Prunes and tubes are decided with the exact predicates Lean uses (exact5d);
// certificates are confirmed exactly at packing time (and by Lean).

#ifndef _NOPERT_SOLVE5D_H
#define _NOPERT_SOLVE5D_H

#include <cstdint>
#include <memory>
#include <atomic>
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
  // If no screened triple certifies, retry with the top max_full * 4, then
  // * 16, up to this many (the center screen can miss the best triple in
  // large pools; 0 disables the retries).
  int max_full_retry = 0;
  // Half-turn prune (exact5d::HalfTurnPruneValid): only for centrally
  // symmetric solids (the deltoidal hexecontahedron).
  bool half_turn_prune = false;
  // Split the box when its widest half-width exceeds split_kappa times the
  // view triangle's angular diameter, else split the view.
  double split_kappa = 0.5;
  // Near the identity (chart 0) a certificate's displacement and its
  // sensitivity to the view both shrink like the rotation, so the box is
  // compared with the view diameter times min(1, view_scale * |center|).
  // 0 disables the scaling (the original rule).
  double view_scale = 0.0;
  // Decide between the box (halved on its widest axis) and the view by
  // lookahead: the best (failed) single triple's worst margin over the
  // children of each. The rule above is the fallback.
  bool view_lookahead = false;
  // Which Cayley axis a box split halves (when the box, not the view, is
  // split): 0 = the widest; 1 = lookahead: the axis whose halves keep the
  // largest worse-half margin for the best (failed) single triple at this
  // node, falling back to the widest when no triple was evaluated; 2 = as
  // 1, but first try to peel: cut (Lean cayleySplitAt, at an eighths point
  // of any axis) so that the larger part, at least min_peel_eighths / 8 of
  // the range and more than half, holds for that triple.
  int split_rule = 0;
  int min_peel_eighths = 5;
  // Nodes deeper than this become deferred (df) leaves.
  int max_depth = 80;
  // When no single triple certifies a node, try a mixture of up to this many
  // triples (Lean's projectiveMixedGlobal); 1 disables mixtures.
  int max_mix_components = 4;
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
// The split choice for a node (its path is not used).
using Split = rows5d::Split;
std::vector<Node> Children(const Node &node, const Split &split);

struct Stats {
  int64_t nodes = 0;
  int64_t ce = 0, mx = 0, tu = 0, pr = 0, pf = 0, df = 0;
  // Certificates whose double margin was positive but which the exact check
  // rejected (a sign the double screen is too optimistic).
  int64_t exact_rejects = 0;
  double worst_margin = 1e300;
  int64_t max_pool_triples = 0;
  void Add(const Stats &o);
};

// Counters shared by concurrent solvers, readable while they run (for
// progress reports); the per-solver Stats are only complete at the end.
struct LiveCounters {
  std::atomic<int64_t> nodes{0}, leaves{0}, tu{0}, df{0};
};

class Solver {
 public:
  Solver(const tubeatlas5d::TubeAtlas *atlas, const Job &job, const Options &opt)
      : atlas_(atlas), job_(job), opt_(opt) {}

  // The cheap leaves only (pr, pf, tu); no certificate search.
  std::optional<rows5d::Leaf> TryPrune(const Node &node) const;
  // Any leaf (prunes first, then a certificate).
  std::optional<rows5d::Leaf> TryLeaf(const Node &node);
  // A view split, or a box split (axis and cut).
  Split ChooseSplit(const Node &node) const;

  // Solves the subtree at `root` depth first. After `max_nodes` nodes (or
  // past opt.max_depth), unexplored nodes become deferred leaves, so the
  // result is always a complete tree.
  std::vector<rows5d::Record> SolveSubtree(const Node &root, int64_t max_nodes);

  const Stats &stats() const { return stats_; }
  // Also count into `live` (may be null) as the search goes.
  void SetLive(LiveCounters *live) { live_ = live; }

 private:
  const contacts5d::ContactPool &Pool(const Node &node);
  // The lookahead axis for split_rule 1, or -1.
  int LookaheadAxis(const Node &node, const geom5d::BoxD &bd) const;
  // For view_lookahead: whether splitting the view beats halving the box on
  // `axis`, or nullopt if there is no failed triple at this node.
  std::optional<bool> ViewBeatsBox(const Node &node, const geom5d::BoxD &bd, int axis) const;
  // The peel cut for split_rule 2, if any.
  std::optional<Split> PeelCut(const Node &node, const geom5d::BoxD &bd) const;

  const tubeatlas5d::TubeAtlas *atlas_;
  Job job_;
  Options opt_;
  Stats stats_;
  LiveCounters *live_ = nullptr;
  // The best single triple of the last node TryLeaf failed to close (for the
  // lookahead split rule). `pool` points into pools_ and is valid until the
  // next Pool() call.
  struct Failed {
    std::string path;
    const contacts5d::ContactPool *pool = nullptr;
    cert5d::Single best;
  };
  Failed last_failed_;
  // Pools of the most recently used views (the depth-first search revisits a
  // view across consecutive box splits). Pools can be large (up to ~C(256,3)
  // triples), so only a few are kept.
  static constexpr size_t kMaxCachedPools = 4;
  std::vector<std::pair<std::string, std::unique_ptr<contacts5d::ContactPool>>> pools_;
};

}  // namespace solve5d

#endif
