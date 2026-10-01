#include "solve5d.h"

#include <algorithm>
#include <cmath>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace solve5d {

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

std::vector<Node> Children(const Node &node, char split) {
  std::vector<Node> out;
  if (split == 'v') {
    for (int c = 0; c < 4; c++) {
      out.push_back(Node{.path = node.path + (char)('0' + c),
                         .tri = geom5d::SplitTriangle(node.tri, c), .box = node.box});
    }
  } else {
    const int axis = split - 'x';
    CHECK(axis >= 0 && axis <= 2) << split;
    out.push_back(Node{.path = node.path + rows5d::BoxStep(axis, false), .tri = node.tri,
                       .box = geom5d::LowerHalf(node.box, axis)});
    out.push_back(Node{.path = node.path + rows5d::BoxStep(axis, true), .tri = node.tri,
                       .box = geom5d::UpperHalf(node.box, axis)});
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
  const cert5d::Single s = cert5d::BestSingle(pool, td, bd, job_.chart, opt_.max_full);
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

char Solver::ChooseSplit(const Node &node) const {
  const geom5d::BoxD bd = geom5d::ToDouble(node.box);
  const int axis = geom5d::WidestAxis(bd);
  if (job_.chart == 0 && geom5d::ContainsOrigin(bd)) {
    // Only the identity tube can close a box containing the identity. If the
    // box is too big for every radius certified below this view, shrink it;
    // otherwise refine the view while the tube table goes deeper (deeper
    // nodes can certify larger radii), and shrink the box past its leaves.
    const auto reached = atlas_->Walk(job_.t, rows5d::ViewPath(node.path));
    const BigRat mismatch = exact5d::IdentityMismatchRadius(geom5d::ToInterval(node.box));
    if (reached.leaf || reached.r_upper < mismatch) return (char)('x' + axis);
    return 'v';
  }
  const double view = geom5d::AngularDiameter(geom5d::ToDouble(node.tri));
  return bd.radius[axis] > opt_.split_kappa * view ? (char)('x' + axis) : 'v';
}

std::vector<rows5d::Record> Solver::SolveSubtree(const Node &root, int64_t max_nodes) {
  std::vector<rows5d::Record> out;
  std::vector<Node> stack = {root};
  int64_t visited = 0;
  while (!stack.empty()) {
    Node node = std::move(stack.back());
    stack.pop_back();
    stats_.nodes++;
    visited++;
    if (visited > max_nodes || (int)node.path.size() > opt_.max_depth) {
      stats_.df++;
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
