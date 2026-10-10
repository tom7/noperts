#include "solve5d.h"

#include <algorithm>
#include <cmath>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace solve5d {

// The lookahead and peel splits only cut axes at least this fraction of the
// widest half-width.
static constexpr double kMinAspect = 0.25;

void Stats::Add(const Stats &o) {
  nodes += o.nodes;
  ce += o.ce;
  mx += o.mx;
  tu += o.tu;
  pr += o.pr;
  pf += o.pf;
  df += o.df;
  exact_rejects += o.exact_rejects;
  max_pool_triples = std::max(max_pool_triples, o.max_pool_triples);
  worst_margin = std::min(worst_margin, o.worst_margin);
}

Node RootNode(const tubeatlas5d::TubeAtlas &atlas, const Job &job) {
  CHECK(job.chart >= 0 && job.chart <= 2);
  return Node{.path = "", .tri = atlas.Triangle(job.t), .box = geom5d::RootBox(job.chart)};
}

std::vector<Node> Children(const Node &node, const Split &split) {
  Split s = split;
  s.path = node.path;
  const auto paths = rows5d::ChildPaths(s);
  std::vector<Node> out;
  for (int k = 0; k < (int)paths.size(); k++) {
    Node c{.path = paths[k], .tri = node.tri, .box = node.box};
    if (s.view) {
      c.tri = geom5d::SplitTriangle(node.tri, k);
    } else if (s.eighths == 4) {
      c.box = k == 0 ? geom5d::LowerHalf(node.box, s.axis) : geom5d::UpperHalf(node.box, s.axis);
    } else {
      c.box = k == 0 ? geom5d::LowerAt(node.box, s.axis, s.eighths)
                     : geom5d::UpperAt(node.box, s.axis, s.eighths);
    }
    out.push_back(std::move(c));
  }
  return out;
}

std::optional<rows5d::Leaf> Solver::TryPrune(const Node &node) const {
  const exact5d::Interval5 iv = geom5d::ToInterval(node.box);
  if (exact5d::OutsideCayleyBall(iv)) return rows5d::RadiusPruneLeaf{};
  for (int dir : {1, -1}) {
    if (exact5d::FundamentalPruneValid(iv, job_.chart, dir)) return rows5d::FundamentalPruneLeaf{dir};
  }
  if (job_.chart == 0) {
    const auto reached = atlas_->Walk(job_.t, rows5d::ViewPath(node.path));
    if (exact5d::IdentityTubeValid(iv, reached.r_lower)) return rows5d::TubeLeaf{reached.r_lower};
  }
  return std::nullopt;
}

const contacts5d::ContactPool &Solver::Pool(const Node &node) {
  const std::string view = rows5d::ViewPath(node.path);
  for (size_t i = 0; i < pools_.size(); i++) {
    if (pools_[i].first == view) {
      // Move to the front (most recently used).
      std::rotate(pools_.begin(), pools_.begin() + i, pools_.begin() + i + 1);
      return *pools_.front().second;
    }
  }
  contacts5d::PoolParams params;
  params.cone_samples = opt_.cone_samples;
  auto pool = std::make_unique<contacts5d::ContactPool>(
      contacts5d::BuildContactPool(geom5d::ToDouble(node.tri), params));
  stats_.max_pool_triples = std::max<int64_t>(stats_.max_pool_triples, pool->triples.size());
  pools_.insert(pools_.begin(), {view, std::move(pool)});
  if (pools_.size() > kMaxCachedPools) pools_.pop_back();
  return *pools_.front().second;
}

std::optional<rows5d::Leaf> Solver::TryLeaf(const Node &node) {
  if (auto p = TryPrune(node)) return p;
  // A box containing the origin of chart 0 contains the identity, which no
  // certificate can rule out; only the tube (or splitting) can.
  const geom5d::BoxD bd = geom5d::ToDouble(node.box);
  if (job_.chart == 0 && geom5d::ContainsOrigin(bd)) return std::nullopt;
  const contacts5d::ContactPool &pool = Pool(node);
  if (pool.triples.empty()) return std::nullopt;
  const geom5d::TriangleD td = geom5d::ToDouble(node.tri);
  cert5d::Single s = cert5d::BestSingle(pool, td, bd, job_.chart, opt_.max_full);
  for (int full = opt_.max_full * 4; !(s.margin > 0) && full <= opt_.max_full_retry &&
                                     full / 4 < (int)pool.triples.size();
       full *= 4) {
    const cert5d::Single wider = cert5d::BestSingle(pool, td, bd, job_.chart, full);
    if (wider.margin > s.margin) s = wider;
  }
  last_failed_ = Failed{.path = node.path, .pool = &pool, .best = s};
  if (s.triple >= 0 && s.margin > 0) {
    bool ok = true;
    if (opt_.exact_check) {
      ok = exact5d::Valid(cert5d::ExactGlobalBox(pool, s, node.tri, node.box, job_.chart));
      if (!ok) stats_.exact_rejects++;
    }
    if (ok) {
      stats_.worst_margin = std::min(stats_.worst_margin, s.margin);
      return rows5d::CertLeaf{.cone_samples = opt_.cone_samples, .triple = s.triple, .inner = s.inner};
    }
  }
  if (opt_.max_mix_components <= 1) return std::nullopt;
  const cert5d::Mixture m = cert5d::BestMixture(pool, td, bd, job_.chart, opt_.max_mix_components);
  if (m.triples.size() < 2 || !(m.margin > 0)) return std::nullopt;
  const std::vector<BigRat> weights = cert5d::RationalWeights(m.w);
  if (opt_.exact_check &&
      !exact5d::Valid(cert5d::ExactMixedBox(pool, m.triples, m.inner, weights, node.tri, node.box,
                                            job_.chart))) {
    stats_.exact_rejects++;
    return std::nullopt;
  }
  stats_.worst_margin = std::min(stats_.worst_margin, m.margin);
  rows5d::MixedLeaf leaf{.cone_samples = opt_.cone_samples};
  for (size_t k = 0; k < m.triples.size(); k++) {
    leaf.components.push_back({.triple = m.triples[k], .inner = m.inner[k], .weight = weights[k]});
  }
  return leaf;
}

int Solver::LookaheadAxis(const Node &node, const geom5d::BoxD &bd) const {
  if (last_failed_.path != node.path || last_failed_.pool == nullptr ||
      last_failed_.best.triple < 0) {
    return -1;
  }
  const contacts5d::ContactPool &pool = *last_failed_.pool;
  const contacts5d::Triple &triple = pool.triples[last_failed_.best.triple];
  const geom5d::TriangleD td = geom5d::ToDouble(node.tri);
  int best_axis = -1;
  double best_score = -1e300;
  // Only axes not much narrower than the widest, so that the box keeps a
  // bounded aspect ratio (halving a thin axis can look as good as any other
  // when the view or the defect, not the box, limits the margin); ties go to
  // the wider axis.
  const int widest = geom5d::WidestAxis(bd);
  for (int a = 0; a < 3; a++) {
    if (bd.radius[a] < kMinAspect * bd.radius[widest]) continue;
    double score = 1e300;
    for (double side : {-1.0, 1.0}) {
      geom5d::BoxD half = bd;
      half.radius[a] *= 0.5;
      half.center[a] += side * half.radius[a];
      score = std::min(score, cert5d::Margin(pool, triple, last_failed_.best.inner, td, half,
                                             job_.chart));
    }
    const double tol = 1e-12 * std::max(1.0, std::abs(best_score));
    if (score > best_score + tol ||
        (score >= best_score - tol && best_axis >= 0 && bd.radius[a] > bd.radius[best_axis])) {
      best_score = std::max(score, best_score);
      best_axis = a;
    }
  }
  return best_axis;
}

std::optional<Split> Solver::PeelCut(const Node &node, const geom5d::BoxD &bd) const {
  if (last_failed_.path != node.path || last_failed_.pool == nullptr ||
      last_failed_.best.triple < 0) {
    return std::nullopt;
  }
  const contacts5d::ContactPool &pool = *last_failed_.pool;
  const contacts5d::Triple &triple = pool.triples[last_failed_.best.triple];
  const geom5d::TriangleD td = geom5d::ToDouble(node.tri);
  // The largest certified part: (its eighths, axis, cut eighths).
  int best_size = std::max(5, opt_.min_peel_eighths) - 1;
  std::optional<Split> best;
  const int widest = geom5d::WidestAxis(bd);
  for (int a = 0; a < 3; a++) {
    if (bd.radius[a] < kMinAspect * bd.radius[widest]) continue;
    const double lo = bd.center[a] - bd.radius[a], width = 2 * bd.radius[a];
    // Lower part [lo, lo + j/8], upper part [lo + (8 - j)/8, hi], each j/8 wide.
    for (int j = 7; j > best_size; j--) {
      for (bool upper : {false, true}) {
        const double cut = lo + width * (upper ? 8 - j : j) / 8.0;
        geom5d::BoxD part = bd;
        const double plo = upper ? cut : lo, phi = upper ? lo + width : cut;
        part.center[a] = 0.5 * (plo + phi);
        part.radius[a] = 0.5 * (phi - plo);
        if (cert5d::Margin(pool, triple, last_failed_.best.inner, td, part, job_.chart) > 0) {
          best_size = j;
          best = Split{.view = false, .axis = a, .eighths = upper ? 8 - j : j};
          break;
        }
      }
    }
  }
  return best;
}

std::optional<bool> Solver::ViewBeatsBox(const Node &node, const geom5d::BoxD &bd,
                                         int axis) const {
  if (last_failed_.path != node.path || last_failed_.pool == nullptr ||
      last_failed_.best.triple < 0) {
    return std::nullopt;
  }
  const contacts5d::ContactPool &pool = *last_failed_.pool;
  const contacts5d::Triple &triple = pool.triples[last_failed_.best.triple];
  const auto &inner = last_failed_.best.inner;
  const geom5d::TriangleD td = geom5d::ToDouble(node.tri);
  double box_score = 1e300;
  for (double side : {-1.0, 1.0}) {
    geom5d::BoxD half = bd;
    half.radius[axis] *= 0.5;
    half.center[axis] += side * half.radius[axis];
    box_score = std::min(box_score, cert5d::Margin(pool, triple, inner, td, half, job_.chart));
  }
  // The pool's defect bounds hold on sub-triangles, so this is conservative.
  double view_score = 1e300;
  for (int k = 0; k < 4; k++) {
    view_score = std::min(view_score, cert5d::Margin(pool, triple, inner,
                                                     geom5d::SplitTriangle(td, k), bd, job_.chart));
  }
  return view_score > box_score;
}

Split Solver::ChooseSplit(const Node &node) const {
  const geom5d::BoxD bd = geom5d::ToDouble(node.box);
  int axis = geom5d::WidestAxis(bd);
  if (job_.chart == 0 && geom5d::ContainsOrigin(bd)) {
    // Only the identity tube can close a box containing the identity. If the
    // box is too big for every radius certified below this view, shrink it;
    // otherwise refine the view while the tube table goes deeper (deeper
    // nodes can certify larger radii), and shrink the box past its leaves.
    const auto reached = atlas_->Walk(job_.t, rows5d::ViewPath(node.path));
    const BigRat mismatch = exact5d::IdentityMismatchRadius(geom5d::ToInterval(node.box));
    if (reached.leaf || reached.r_upper < mismatch) return Split{.view = false, .axis = axis};
    return Split{.view = true};
  }
  double view = geom5d::AngularDiameter(geom5d::ToDouble(node.tri));
  if (job_.chart == 0 && opt_.view_scale > 0) {
    view *= std::min(1.0, opt_.view_scale * yocto::length(bd.center));
  }
  if (opt_.view_lookahead) {
    if (auto v = ViewBeatsBox(node, bd, axis)) {
      if (*v) return Split{.view = true};
      return Split{.view = false, .axis = axis};
    }
  }
  if (!(bd.radius[axis] > opt_.split_kappa * view)) return Split{.view = true};
  if (opt_.split_rule >= 2) {
    if (auto cut = PeelCut(node, bd)) return *cut;
  }
  if (opt_.split_rule >= 1) {
    const int a = LookaheadAxis(node, bd);
    if (a >= 0) axis = a;
  }
  return Split{.view = false, .axis = axis};
}

std::vector<rows5d::Record> Solver::SolveSubtree(const Node &root, int64_t max_nodes) {
  std::vector<rows5d::Record> out;
  std::vector<Node> stack = {root};
  int64_t visited = 0;
  while (!stack.empty()) {
    Node node = std::move(stack.back());
    stack.pop_back();
    stats_.nodes++;
    if (live_ != nullptr) live_->nodes++;
    visited++;
    if (visited > max_nodes || (int)node.path.size() > opt_.max_depth) {
      stats_.df++;
      if (live_ != nullptr) live_->df++;
      out.push_back({node.path, rows5d::DeferredLeaf{}});
      continue;
    }
    if (auto leaf = TryLeaf(node)) {
      std::visit(
          [&](const auto &l) {
            using T = std::decay_t<decltype(l)>;
            if constexpr (std::is_same_v<T, rows5d::CertLeaf>) stats_.ce++;
            if constexpr (std::is_same_v<T, rows5d::MixedLeaf>) stats_.mx++;
            if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) stats_.tu++;
            if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) stats_.pr++;
            if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) stats_.pf++;
          },
          *leaf);
      if (live_ != nullptr) {
        live_->leaves++;
        if (std::holds_alternative<rows5d::TubeLeaf>(*leaf)) live_->tu++;
      }
      out.push_back({node.path, *leaf});
      continue;
    }
    auto children = Children(node, ChooseSplit(node));
    // Push in reverse so children are visited in order.
    for (auto it = children.rbegin(); it != children.rend(); ++it) stack.push_back(std::move(*it));
  }
  return out;
}

}  // namespace solve5d
