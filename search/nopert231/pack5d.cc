// Packs 5D search journals into a Lean global table for one chart
// (PackedSolutionTree.decodeTable: count, intervals, triangles, rows).
//
// Full table (--all): row 0 is codeRoot over every code triangle (tag 10),
// with each job's tree below it; every job must be complete (no deferred
// leaves). Single job (--t T): row 0 is the job's root node; such a table is
// not a Table.Valid chart table, but each row can be checked with Lean's
// row checker (check_global_rows in Noperthedron) during development.
//
// Rows follow the tree in breadth-first order (Lean needs children after
// their parents). Certificate leaves rebuild their contact pool from the
// recorded cone_samples to produce the exact Lean certificate. Certificates
// are moved onto dyadic outer view triangles (Lean regionRelax, tag 11)
// wherever they hold exactly there; --exact_check also confirms the ones
// kept on their exact triangle.
//
// Per code (--per_code DIR): one pack per job, DIR/c<C>/t<T>.pack, each like
// a --t pack (row 0 is the job's root). Lean's decodeCodeTables concatenates
// them behind a codeRoot row into the chart table, so a re-searched code
// only needs its own pack (and check) redone: packs newer than their journal
// are skipped unless --force.
//
// Usage: pack5d.exe --chart C (--all | --t T | --per_code DIR) [--journals jobs]
//                   [--out FILE] [--trees_dir trees_r2] [--bdd codebdd231.json]
//                   [--exact_check] [--threads 8] [--force]

#include <atomic>
#include <algorithm>
#include <mutex>
#include <filesystem>
#include <chrono>
#include <cstdio>
#include <deque>
#include <format>
#include <fstream>
#include <map>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "cert5d.h"
#include "contacts5d.h"
#include "exact5d.h"
#include "geom5d.h"
#include "rows5d.h"
#include "solve5d.h"
#include "threadutil.h"
#include "tubeatlas5d.h"

namespace {

std::string Zigzag(const BigRat &r) {
  const BigInt num = r.Numerator();
  const BigInt den = r.Denominator();
  const BigInt zz = (num >= BigInt(0)) ? (num * 2) : ((BigInt(0) - num) * 2 - 1);
  return zz.ToString() + "," + den.ToString();
}

class Packer {
 public:
  Packer(const tubeatlas5d::TubeAtlas &atlas, int chart, bool exact_check)
      : atlas_(atlas), chart_(chart), exact_check_(exact_check) {}

  // The pack encoding of an interval or a triangle (also its dedup key).
  static std::string IntervalString(const geom5d::BoxQ &b) {
    std::string s;
    for (int a = 0; a < 3; a++) s += "," + Zigzag((b.lo[a] + b.hi[a]) / BigRat(2));
    for (int a = 0; a < 3; a++) s += "," + Zigzag((b.hi[a] - b.lo[a]) / BigRat(2));
    return s;
  }
  static std::string TriangleString(const exact5d::TriangleQ &t) {
    std::string s;
    for (int i = 0; i < 3; i++) for (int c = 0; c < 3; c++) s += "," + Zigzag(t[i][c]);
    return s;
  }

  // Table indices, numbered in order of first use.
  int IntervalId(const std::string &s) {
    auto [it, fresh] = interval_ids_.emplace(s, (int)intervals_.size());
    if (fresh) intervals_.push_back(s);
    return it->second;
  }
  int TriangleId(const std::string &s) {
    auto [it, fresh] = triangle_ids_.emplace(s, (int)triangles_.size());
    if (fresh) triangles_.push_back(s);
    return it->second;
  }

  // Appends the rows of job t's tree; returns the id of its root row.
  //
  // Certificate leaves are checked over geom5d::OuterDyadicTriangle of their
  // view triangle (Lean Row.regionRelax), which is much cheaper in Lean than
  // the exact triangle. A regionRelax row goes at the top of each maximal
  // subtree that has no view splits and no tube leaves, contains a
  // certificate, and whose certificates all hold exactly over the outer
  // triangle (checked here with exact5d, at about the cost of building them).
  //
  // The exact arithmetic (view triangles with ~1000-bit corners, their outer
  // triangles, boxes, encodings, certificates) runs in parallel; only the
  // table numbering is sequential, in row order.
  int AddJob(int t, const rows5d::Tree &tree, int first_id) {
    const solve5d::Node root = solve5d::RootNode(atlas_, {.t = t, .chart = chart_});
    std::unordered_map<std::string, const rows5d::Split *> split_at;
    for (const auto &s : tree.splits) split_at[s.path] = &s;
    std::unordered_map<std::string, const rows5d::Leaf *> leaf_at;
    for (const auto &r : tree.leaves) leaf_at[r.path] = &r.leaf;

    // Nodes in breadth-first order (so depth never decreases), with their
    // parents and views; boxes and triangles are filled in below.
    struct N {
      std::string path;
      int parent = -1;
      int depth = 0;
      int child = 0;  // index among the parent's children
      const rows5d::Split *split = nullptr;
      const rows5d::Leaf *leaf = nullptr;
      std::vector<int> kids;
      int view = 0;  // index into views
      geom5d::BoxQ box;
    };
    struct View {
      int parent = -1, child = 0, depth = 0;
      exact5d::TriangleQ exact, outer;
      std::string exact_str, outer_str;
    };
    std::vector<N> nodes;
    std::vector<View> views(1);
    views[0].exact = root.tri;
    nodes.push_back({.path = "", .view = 0, .box = root.box});
    for (size_t q = 0; q < nodes.size(); q++) {
      auto it = split_at.find(nodes[q].path);
      if (it == split_at.end()) {
        nodes[q].leaf = leaf_at.at(nodes[q].path);
        continue;
      }
      const rows5d::Split &s = *it->second;
      nodes[q].split = &s;
      const auto kids = rows5d::ChildPaths(s);
      for (int k = 0; k < (int)kids.size(); k++) {
        N c{.path = kids[k], .parent = (int)q, .depth = nodes[q].depth + 1, .child = k};
        if (s.view) {
          c.view = views.size();
          views.push_back({.parent = nodes[q].view, .child = k,
                           .depth = views[nodes[q].view].depth + 1});
        } else {
          c.view = nodes[q].view;
        }
        nodes[q].kids.push_back(nodes.size());
        nodes.push_back(std::move(c));
      }
    }
    // Calls f(i) for every element, level by level (each level after its
    // parents' level), in parallel within a level.
    auto by_levels = [&](size_t n, auto depth_of, const auto &f) {
      size_t lo = 0;
      while (lo < n) {
        size_t hi = lo;
        while (hi < n && depth_of(hi) == depth_of(lo)) hi++;
        ParallelComp(hi - lo, [&](int64_t k) { f(lo + k); }, threads_);
        lo = hi;
      }
    };
    const auto job_start = std::chrono::steady_clock::now();
    auto phase = [&](const char *what) {
      if (nodes.size() < 1000000) return;
      printf("  t=%d: %s (%.0fs)\n", t, what,
             std::chrono::duration<double>(std::chrono::steady_clock::now() - job_start).count());
      fflush(stdout);
    };
    phase(std::format("{} nodes, {} views", nodes.size(), views.size()).c_str());
    by_levels(nodes.size(), [&](size_t n) { return nodes[n].depth; }, [&](size_t n) {
      N &node = nodes[n];
      if (node.parent < 0) return;
      const N &p = nodes[node.parent];
      const rows5d::Split &s = *p.split;
      if (s.view) {
        node.box = p.box;
      } else if (s.eighths == 4) {
        node.box = node.child == 0 ? geom5d::LowerHalf(p.box, s.axis)
                                   : geom5d::UpperHalf(p.box, s.axis);
      } else {
        node.box = node.child == 0 ? geom5d::LowerAt(p.box, s.axis, s.eighths)
                                   : geom5d::UpperAt(p.box, s.axis, s.eighths);
      }
    });
    by_levels(views.size(), [&](size_t v) { return views[v].depth; }, [&](size_t v) {
      View &view = views[v];
      if (view.parent >= 0) view.exact = geom5d::SplitTriangle(views[view.parent].exact, view.child);
      view.outer = geom5d::OuterDyadicTriangle(view.exact);
      view.exact_str = TriangleString(view.exact);
      view.outer_str = TriangleString(view.outer);
    });

    phase("boxes and view triangles done");
    // Certificate leaves, built over the outer triangle (and checked), or
    // over the exact one if that fails. Grouped by view to share the pool.
    struct Built {
      bool outer_ok = false;
      std::string body;  // the row after its triangle index
    };
    std::vector<Built> built_rows(nodes.size());
    std::map<int, std::vector<int>> cert_by_view;
    for (int n = 0; n < (int)nodes.size(); n++) {
      if (nodes[n].leaf != nullptr && IsCertificate(*nodes[n].leaf)) {
        cert_by_view[nodes[n].view].push_back(n);
      }
    }
    std::vector<const std::vector<int> *> groups;
    for (const auto &[v, g] : cert_by_view) groups.push_back(&g);
    std::atomic<int64_t> relax_failures = 0;
    ParallelComp(groups.size(), [&](int64_t gi) {
      const std::vector<int> &group = *groups[gi];
      const View &view = views[nodes[group[0]].view];
      std::map<int, contacts5d::ContactPool> pools;  // by cone_samples
      auto pool_for = [&](int cone_samples) -> const contacts5d::ContactPool & {
        auto it = pools.find(cone_samples);
        if (it == pools.end()) {
          contacts5d::PoolParams params;
          params.cone_samples = cone_samples;
          it = pools.emplace(cone_samples,
                             contacts5d::BuildContactPool(geom5d::ToDouble(view.exact), params))
                   .first;
        }
        return it->second;
      };
      for (int n : group) {
        Built &b = built_rows[n];
        bool ok = false;
        b.body = CertBody(nodes[n].path, *nodes[n].leaf, view.outer, nodes[n].box, pool_for,
                          /*check=*/true, &ok);
        if (ok) {
          b.outer_ok = true;
          continue;
        }
        relax_failures++;
        b.body = CertBody(nodes[n].path, *nodes[n].leaf, view.exact, nodes[n].box, pool_for,
                          exact_check_, &ok);
        CHECK(ok) << "certificate fails exactly at " << nodes[n].path;
      }
    }, threads_);
    if (relax_failures > 0) {
      printf("t=%d: %lld certificates fail over the outer triangle; kept exact\n", t,
             (long long)relax_failures.load());
    }

    phase("certificates built");
    // Relaxable subtrees, bottom-up (children come after parents).
    std::vector<char> relaxable(nodes.size(), 0), has_cert(nodes.size(), 0);
    for (int n = (int)nodes.size() - 1; n >= 0; n--) {
      const N &node = nodes[n];
      if (node.split != nullptr) {
        bool r = !node.split->view, c = false;
        for (int k : node.kids) r = r && relaxable[k], c = c || has_cert[k];
        relaxable[n] = r;
        has_cert[n] = c;
      } else if (IsCertificate(*node.leaf)) {
        relaxable[n] = built_rows[n].outer_ok;
        has_cert[n] = 1;
      } else {
        // Prune rows do not depend on their region.
        relaxable[n] = std::holds_alternative<rows5d::RadiusPruneLeaf>(*node.leaf) ||
                       std::holds_alternative<rows5d::FundamentalPruneLeaf>(*node.leaf);
      }
    }
    auto relax_point = [&](int n) {
      return relaxable[n] && has_cert[n] && (n == 0 || !relaxable[nodes[n].parent]);
    };

    // Ids: breadth-first, with a relax point's regionRelax row just before
    // its content row.
    std::vector<int> id_of(nodes.size()), content_id(nodes.size());
    std::vector<char> relaxed(nodes.size(), 0);  // region uses the outer triangle
    int next = first_id;
    for (int n = 0; n < (int)nodes.size(); n++) {
      id_of[n] = next++;
      content_id[n] = relax_point(n) ? next++ : id_of[n];
      relaxed[n] = relax_point(n) || (n > 0 && relaxed[nodes[n].parent]);
    }
    // Interval encodings in parallel; then table numbers in row order.
    std::vector<std::string> iv_str(nodes.size());
    ParallelComp(nodes.size(), [&](int64_t n) { iv_str[n] = IntervalString(nodes[n].box); },
                 threads_);
    std::vector<int> iv_of(nodes.size()), tri_of(nodes.size()), exact_tri(nodes.size(), -1),
        outer_tri(nodes.size(), -1);
    for (int n = 0; n < (int)nodes.size(); n++) {
      const View &view = views[nodes[n].view];
      iv_of[n] = IntervalId(iv_str[n]);
      if (relax_point(n)) {
        exact_tri[n] = TriangleId(view.exact_str);
        outer_tri[n] = TriangleId(view.outer_str);
        relax_rows_++;
      }
      tri_of[n] = TriangleId(relaxed[n] ? view.outer_str : view.exact_str);
    }
    std::vector<std::string>().swap(iv_str);
    // Rows in parallel.
    std::vector<std::string> out(nodes.size()), relax_out(nodes.size());
    ParallelComp(nodes.size(), [&](int64_t n) {
      const N &node = nodes[n];
      const int iv = iv_of[n];
      std::string row;
      if (relax_point(n)) {
        relax_out[n] = std::format(",11,{},{},{},0,{},{}", id_of[n], iv, content_id[n],
                                   exact_tri[n], outer_tri[n]);
      }
      const int id = content_id[n];
      const int region = tri_of[n];
      if (node.split != nullptr) {
        const std::vector<int> &k = node.kids;
        if (node.split->view) {
          row += std::format(",2,{},{},{},{},{},{},0,{}", id, iv, id_of[k[0]], id_of[k[1]],
                             id_of[k[2]], id_of[k[3]], region);
        } else if (node.split->eighths == 4) {
          row += std::format(",1,{},{},{},{},{},0,{}", id, iv, id_of[k[0]], id_of[k[1]],
                             node.split->axis + 2, region);
        } else {
          // Lean cayleySplitAt.
          row += std::format(",12,{},{},{},{},{},{},0,{}", id, iv, id_of[k[0]], id_of[k[1]],
                             node.split->axis + 2,
                             Zigzag(geom5d::CutPoint(node.box, node.split->axis, node.split->eighths)),
                             region);
        }
      } else if (IsCertificate(*node.leaf)) {
        // Each certificate is used over the triangle it was built for.
        CHECK(relaxed[n] == built_rows[n].outer_ok) << node.path;
        const char *tag = std::holds_alternative<rows5d::CertLeaf>(*node.leaf) ? "4" : "9";
        row += std::format(",{},{},{},0,{}", tag, id, iv, region) + built_rows[n].body;
      } else {
        row += OtherLeafRow(t, node.path, *node.leaf, id, iv, region);
      }
      out[n] = std::move(row);
    }, threads_);
    for (size_t n = 0; n < nodes.size(); n++) {
      if (!relax_out[n].empty()) rows_.push_back(std::move(relax_out[n]));
      rows_.push_back(std::move(out[n]));
    }
    return first_id;
  }

  int64_t RelaxRows() const { return relax_rows_; }
  void SetThreads(int threads) { threads_ = threads; }

  void AddCodeRoot(const std::vector<int> &children) {
    std::string row = std::format(",10,0,{},{}", IntervalId(IntervalString(geom5d::RootBox(chart_))),
                                  children.size());
    for (int c : children) row += std::format(",{}", c);
    rows_.insert(rows_.begin(), row);
  }

  void Write(const std::string &path) const {
    std::ofstream f(path, std::ios::binary);
    CHECK(f.good()) << path;
    f << rows_.size() << "," << intervals_.size();
    for (const auto &s : intervals_) f << s;
    f << "," << triangles_.size();
    for (const auto &s : triangles_) f << s;
    for (const auto &r : rows_) f << r;
    f << "\n";
  }

  size_t NumRows() const { return rows_.size(); }

 private:
  static bool IsCertificate(const rows5d::Leaf &leaf) {
    return std::holds_alternative<rows5d::CertLeaf>(leaf) ||
           std::holds_alternative<rows5d::MixedLeaf>(leaf);
  }

  // The part of a certificate leaf's row after its triangle index, built
  // over `tri`. With `check`, *ok says whether it holds exactly (exact5d);
  // otherwise *ok is true.
  template <class PoolFor>
  std::string CertBody(const std::string &path, const rows5d::Leaf &leaf,
                       const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                       const PoolFor &pool_for, bool check, bool *ok) const {
    if (const auto *l = std::get_if<rows5d::CertLeaf>(&leaf)) {
      const auto &pool = pool_for(l->cone_samples);
      CHECK(l->triple < (int)pool.triples.size()) << "stale triple index at " << path;
      const cert5d::Single s{.triple = l->triple, .inner = l->inner};
      const exact5d::GlobalBox g = cert5d::ExactGlobalBox(pool, s, tri, box, chart_);
      *ok = !check || exact5d::Valid(g);
      const auto &c = g.certificate;
      std::string r;
      for (const auto *arr : {&c.edge_start, &c.edge_finish, &c.edge_start2, &c.edge_finish2,
                              &c.mix, &c.index, &c.nonzero_witness}) {
        for (int m = 0; m < 3; m++) r += std::format(",{}", (*arr)[m]);
      }
      r += "," + Zigzag(c.B);
      for (int m = 0; m < 3; m++) r += std::format(",{}", g.inner_index[m]);
      r += "," + Zigzag(g.ball_multiplier);
      return r;
    }
    const auto &l = std::get<rows5d::MixedLeaf>(leaf);
    const auto &pool = pool_for(l.cone_samples);
    std::vector<int> triples;
    std::vector<std::array<int, 3>> inner;
    std::vector<BigRat> weights;
    for (const auto &c : l.components) {
      CHECK(c.triple < (int)pool.triples.size()) << "stale triple index at " << path;
      triples.push_back(c.triple);
      inner.push_back(c.inner);
      weights.push_back(c.weight);
    }
    const exact5d::MixedBox m =
        cert5d::ExactMixedBox(pool, triples, inner, weights, tri, box, chart_);
    *ok = !check || exact5d::Valid(m);
    std::string r;
    for (int k = 0; k < 4; k++) r += "," + Zigzag(m.weight[k]);
    for (int k = 0; k < 4; k++) {
      const auto &c = m.component[k].certificate;
      for (const auto *arr : {&c.edge_start, &c.edge_finish, &c.edge_start2, &c.edge_finish2,
                              &c.mix, &c.index, &c.nonzero_witness}) {
        for (int i = 0; i < 3; i++) r += std::format(",{}", (*arr)[i]);
      }
      r += "," + Zigzag(c.B);
      for (int i = 0; i < 3; i++) r += std::format(",{}", m.component[k].inner_index[i]);
      r += "," + Zigzag(m.component[k].ball_multiplier);
    }
    return r;
  }

  // Rows of the other leaves (tube, radius prune, fundamental prune).
  std::string OtherLeafRow(int t, const std::string &path, const rows5d::Leaf &leaf, int id,
                           int iv, int tri_id) const {
    return std::visit(
        [&](const auto &l) -> std::string {
          using T = std::decay_t<decltype(l)>;
          if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) {
            const std::string view = rows5d::ViewPath(path);
            std::string r =
                std::format(",6,{},{},0,{},{},{}", id, iv, Zigzag(l.r), t, view.size());
            for (char c : view) r += std::format(",{}", c - '0');
            r += std::format(",0,{}", tri_id);
            return r;
          } else if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) {
            return std::format(",7,{},{},0,{}", id, iv, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) {
            return std::format(",8,{},{},{},0,{}", id, iv, l.direction > 0 ? 1 : 0, tri_id);
          } else if constexpr (std::is_same_v<T, rows5d::DeferredLeaf>) {
            LOG(FATAL) << "deferred leaf " << path << " (job t=" << t
                       << "): finish the search before packing";
            return "";
          } else {
            LOG(FATAL) << "certificate leaf " << path << " has no built row";
            return "";
          }
        },
        leaf);
  }

  const tubeatlas5d::TubeAtlas &atlas_;
  int chart_;
  bool exact_check_;
  int threads_ = 8;
  int64_t relax_rows_ = 0;
  std::vector<std::string> rows_;
  std::vector<std::string> intervals_, triangles_;
  std::unordered_map<std::string, int> interval_ids_, triangle_ids_;
};

}  // namespace

namespace {

// Reads a job's journal and builds its tree.
rows5d::Tree ReadTree(const std::string &journals, int chart, int t) {
  const auto j = rows5d::ReadJournal(std::format("{}/c{}/t{}.journal", journals, chart, t));
  CHECK(!j.leaves.empty()) << "no journal for t=" << t << " chart=" << chart;
  auto built = rows5d::BuildTree(j.leaves);
  CHECK(std::holds_alternative<rows5d::Tree>(built))
      << "job t=" << t << " chart=" << chart << ": " << std::get<std::string>(built);
  return std::move(std::get<rows5d::Tree>(built));
}

// Packs each job (t in `jobs`) to its own file under out_dir, skipping
// packs newer than their journal unless `force`. Large jobs go one at a
// time with all threads; the rest run concurrently, one thread each.
void PackPerCode(const tubeatlas5d::TubeAtlas &atlas, int chart, bool exact_check,
                 const std::string &journals, const std::string &out_dir,
                 const std::vector<int> &jobs, bool force, int threads) {
  namespace fs = std::filesystem;
  fs::create_directories(std::format("{}/c{}", out_dir, chart));
  struct Job {
    int t;
    uintmax_t journal_bytes;
  };
  std::vector<Job> todo;
  for (int t : jobs) {
    const fs::path journal = std::format("{}/c{}/t{}.journal", journals, chart, t);
    const fs::path pack = std::format("{}/c{}/t{}.pack", out_dir, chart, t);
    CHECK(fs::exists(journal)) << "no journal " << journal;
    if (!force && fs::exists(pack) && fs::last_write_time(pack) > fs::last_write_time(journal)) {
      continue;
    }
    todo.push_back({t, fs::file_size(journal)});
  }
  std::sort(todo.begin(), todo.end(),
            [](const Job &a, const Job &b) { return a.journal_bytes > b.journal_bytes; });
  printf("%zu of %zu code packs to write\n", todo.size(), jobs.size());
  fflush(stdout);
  std::mutex out_mu;
  std::atomic<int> done = 0;
  auto pack_one = [&](const Job &job, int job_threads) {
    const rows5d::Tree tree = ReadTree(journals, chart, job.t);
    Packer packer(atlas, chart, exact_check);
    packer.SetThreads(job_threads);
    packer.AddJob(job.t, tree, 0);
    const std::string path = std::format("{}/c{}/t{}.pack", out_dir, chart, job.t);
    // Write then rename, so a pack that exists is complete.
    packer.Write(path + ".tmp");
    fs::rename(path + ".tmp", path);
    std::lock_guard<std::mutex> l(out_mu);
    printf("[%d/%zu] wrote %s: %zu rows (%lld regionRelax)\n", ++done, todo.size(),
           path.c_str(), packer.NumRows(), (long long)packer.RelaxRows());
    fflush(stdout);
  };
  // Journals above this size get all threads to themselves.
  constexpr uintmax_t kLarge = 20'000'000;
  size_t k = 0;
  for (; k < todo.size() && todo[k].journal_bytes > kLarge; k++) pack_one(todo[k], threads);
  ParallelComp(todo.size() - k, [&](int64_t i) { pack_one(todo[k + i], 1); }, threads);
}

}  // namespace

int main(int argc, char **argv) {
  int chart = -1, single = -1, threads = 8;
  bool all = false, exact_check = false, force = false;
  std::string journals = "jobs", out, trees_dir = "trees_r2", bdd = "codebdd231.json", per_code;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--chart") chart = std::stoi(next());
    else if (a == "--t") single = std::stoi(next());
    else if (a == "--all") all = true;
    else if (a == "--per_code") per_code = next();
    else if (a == "--journals") journals = next();
    else if (a == "--out") out = next();
    else if (a == "--trees_dir") trees_dir = next();
    else if (a == "--bdd") bdd = next();
    else if (a == "--exact_check") exact_check = true;
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--force") force = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(chart >= 0 && chart <= 2) << "--chart 0..2";

  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  if (!per_code.empty()) {
    CHECK(!all) << "--per_code packs every job (or the --t job)";
    std::vector<int> jobs;
    if (single >= 0) {
      jobs.push_back(single);
    } else {
      for (int t = 0; t < atlas.NumTriangles(); t++) jobs.push_back(t);
    }
    PackPerCode(atlas, chart, exact_check, journals, per_code, jobs, force, threads);
    return 0;
  }
  CHECK(all != (single >= 0)) << "exactly one of --all, --t, --per_code";
  if (out.empty()) out = all ? std::format("chart{}.pack", chart) : std::format("chart{}.t{}.pack", chart, single);

  Packer packer(atlas, chart, exact_check);
  packer.SetThreads(threads);
  // Journals are read and turned into trees in parallel.
  std::vector<int> jobs;
  if (all) {
    for (int t = 0; t < atlas.NumTriangles(); t++) jobs.push_back(t);
  } else {
    jobs.push_back(single);
  }
  std::vector<rows5d::Tree> trees(jobs.size());
  ParallelComp(jobs.size(), [&](int64_t k) { trees[k] = ReadTree(journals, chart, jobs[k]); },
               threads);
  printf("read %zu job trees\n", trees.size());
  fflush(stdout);
  if (all) {
    std::vector<int> roots;
    int next_id = 1;  // row 0 is the code root
    for (size_t k = 0; k < jobs.size(); k++) {
      const size_t before = packer.NumRows();
      roots.push_back(packer.AddJob(jobs[k], trees[k], next_id));
      next_id += packer.NumRows() - before;
      printf("[%zu/%zu jobs] t=%d: %zu rows (total %zu)\n", k + 1, jobs.size(), jobs[k],
             packer.NumRows() - before, packer.NumRows());
      fflush(stdout);
      rows5d::Tree().splits.swap(trees[k].splits);
      std::vector<rows5d::Record>().swap(trees[k].leaves);
    }
    packer.AddCodeRoot(roots);
  } else {
    packer.AddJob(single, trees[0], 0);
  }
  packer.Write(out);
  printf("wrote %s: %zu rows (%lld regionRelax)\n", out.c_str(), packer.NumRows(),
         (long long)packer.RelaxRows());
  return 0;
}
