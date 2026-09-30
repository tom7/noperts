// Identity-tube certificate synthesis for the 79 face-visibility code cells
// of Nopert #229 (see notes/Q.md). For each projective triangle of each
// code cell (from codebdd229.json) we build a quadtree whose leaves carry
// pure Tag 1 (4-axis cage) certificates, audited in exact arithmetic
// with the same conditions as Lean's Box.ViewValid.
//
// The solver is restartable: every certified leaf ("L") and every split
// ("S") is appended to trees/code.<X>.journal as soon as it is decided.
// On restart the journal is replayed and only the pending frontier is
// worked on. Leaves are re-audited on replay, so a journal can never
// inject an unchecked certificate. When every triangle of a code is
// complete, the tree is written to trees/tree.<X>.json (the format read
// by export_codetrees_pack).
//
// With --import, a code with no journal is seeded from its existing
// tree.<X>.json: split nodes and Tag 1 leaves are kept (and re-audited);
// any other leaves (e.g. Tag 2) become pending again.

#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstdio>
#include <filesystem>
#include <functional>
#include <iostream>
#include <map>
#include <mutex>
#include <optional>
#include <string>
#include <thread>
#include <vector>

#include "rapidjson/document.h"
#include "util.h"
#include "yocto-math.h"
#include "nopert229.h"
#include "bignum/big.h"
#include "bignum/big-vec.h"
#include "bignum/big-overloads.h"

using vec3 = yocto::vec<double, 3>;

#define TUBECERT_NO_MAIN
#include "tubecert229.cc"

#include "tubetree229.h"

using namespace tubetree229;

struct SolverOptions {
  std::string bdd_json = "codebdd229.json";
  std::string output_dir = "trees";
  int code_id = -1; // -1 means all
  int tri_id = -1;  // -1 means all triangles of the code
  int num_threads = 16;
  int max_depth = 30;
  BigRat target_c{0}; // Any positive rational c > 0
  BigRat target_r{0}; // Any positive rational r > 0
  bool force = false;
  bool import_tree = false;
};

// Find best cage for a given triangle, pre-validating AuditAxis on tri
static bool FindBestCageForTriangle(
    const TriangleQ &tri,
    unsigned int *seed,
    LocalCertificate *out_cert,
    double *out_margin) {

  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  vec3 center = (c0 + c1 + c2) / 3.0;
  double clen = yocto::length(center);
  if (clen < 1e-12) return false;
  center = center / clen;

  std::vector<CandidateTriple> candidates;
  GenerateCandidatesForView(center, tri, 8, true, 1e-13, &candidates);
  if (candidates.size() < 4) return false;

  std::vector<vec3> pts;
  for (const auto &cand : candidates) pts.push_back(cand.normalized_a);

  // Axis audits are exact and expensive; memoize them per candidate.
  std::vector<int8_t> audit_ok(candidates.size(), -1);
  auto Audited = [&](int idx) {
    if (audit_ok[idx] < 0) {
      ContactInfo cts[3] = {candidates[idx].contacts[0],
                            candidates[idx].contacts[1],
                            candidates[idx].contacts[2]};
      AxisCertificate ax;
      BigVecQ3 cent;
      BigRat del;
      audit_ok[idx] = AuditAxis(tri, cts, &ax, &cent, &del, nullptr) ? 1 : 0;
    }
    return audit_ok[idx] == 1;
  };

  double best_margin = 0.0;
  std::array<int, 4> best_tet = {-1, -1, -1, -1};
  int N = pts.size();

  // 1. Search for maximal margin cage via trials
  for (int trial = 0; trial < 25000; trial++) {
    int i0 = rand_r(seed) % N, i1 = rand_r(seed) % N, i2 = rand_r(seed) % N, i3 = rand_r(seed) % N;
    if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
    vec3 tpts[4] = {pts[i0], pts[i1], pts[i2], pts[i3]};
    double margin;
    double bary[4];
    if (TetrahedronOriginMargin(tpts, &margin, bary) && margin > best_margin) {
      if (Audited(i0) && Audited(i1) && Audited(i2) && Audited(i3)) {
        best_margin = margin;
        best_tet = {i0, i1, i2, i3};
      }
    }
  }

  // 2. Fallback to Wolfe algorithm if no positive-margin audited cage found
  if (best_margin <= 0) {
    std::array<int, 4> wolfe_tet;
    if (FindBalancedTetrahedron(pts, &wolfe_tet, false)) {
      vec3 tpts[4] = {pts[wolfe_tet[0]], pts[wolfe_tet[1]], pts[wolfe_tet[2]], pts[wolfe_tet[3]]};
      double margin;
      double bary[4];
      if (TetrahedronOriginMargin(tpts, &margin, bary) && margin > 0) {
        bool all_ok = true;
        for (int idx : wolfe_tet) all_ok = all_ok && Audited(idx);
        if (all_ok) {
          best_margin = margin;
          best_tet = wolfe_tet;
        }
      }
    }
  }

  if (best_margin <= 0) return false;

  for (int a = 0; a < 4; a++) {
    out_cert->axes[a].contacts[0] = candidates[best_tet[a]].contacts[0];
    out_cert->axes[a].contacts[1] = candidates[best_tet[a]].contacts[1];
    out_cert->axes[a].contacts[2] = candidates[best_tet[a]].contacts[2];
  }
  *out_margin = best_margin;
  return true;
}

// ---------------- Journal ----------------

// Journal lines (one record per line, space separated):
//   L <tri> <path> <sym> <72 ints: 4 axes x 3 contacts x
//                          (edge_start edge_finish edge_start2 edge_finish2 mix vertex)>
//   S <tri> <path>
// The root path is written as ".". A truncated final line is ignored.

static std::string PathToken(const std::string &path) {
  return path.empty() ? "." : path;
}

static std::string LeafLine(int tri, const std::string &path, const LocalCertificate &cert) {
  std::string s = StringPrintf("L %d %s %d", tri, PathToken(path).c_str(), cert.symmetry_index);
  for (int a = 0; a < 4; a++) {
    for (int k = 0; k < 3; k++) {
      const ContactInfo &c = cert.axes[a].contacts[k];
      StringAppendF(&s, " %d %d %d %d %d %d", c.edge_start, c.edge_finish,
                    c.edge_start2, c.edge_finish2, c.mix, c.vertex);
    }
  }
  s += "\n";
  return s;
}

struct JournalRecord {
  bool is_split = false;
  LocalCertificate cert; // contacts only (for leaves)
};

// Key: (triangle index, path).
using JournalMap = std::map<std::pair<int, std::string>, JournalRecord>;

static bool ParseJournalLine(const std::string &line, int *tri, std::string *path,
                             JournalRecord *rec) {
  std::vector<std::string> tok = Util::Tokens(line, [](char c) { return c == ' '; });
  if (tok.size() < 3) return false;
  *tri = atoi(tok[1].c_str());
  *path = tok[2] == "." ? "" : tok[2];
  for (char c : *path) if (c < '0' || c > '3') return false;
  if (tok[0] == "S") {
    if (tok.size() != 3) return false;
    rec->is_split = true;
    return true;
  }
  if (tok[0] != "L" || tok.size() != 4 + 72) return false;
  rec->is_split = false;
  rec->cert.symmetry_index = atoi(tok[3].c_str());
  int t = 4;
  for (int a = 0; a < 4; a++) {
    for (int k = 0; k < 3; k++) {
      ContactInfo &c = rec->cert.axes[a].contacts[k];
      c.edge_start = atoi(tok[t++].c_str());
      c.edge_finish = atoi(tok[t++].c_str());
      c.edge_start2 = atoi(tok[t++].c_str());
      c.edge_finish2 = atoi(tok[t++].c_str());
      c.mix = atoi(tok[t++].c_str());
      c.vertex = atoi(tok[t++].c_str());
    }
  }
  return true;
}

static JournalMap ReadJournal(const std::string &filename) {
  JournalMap m;
  if (!std::filesystem::exists(filename)) return m;
  std::string content = Util::ReadFile(filename);
  size_t pos = 0;
  int bad = 0;
  while (pos < content.size()) {
    size_t nl = content.find('\n', pos);
    // Without a newline, the last record was cut off mid-write.
    if (nl == std::string::npos) { bad++; break; }
    std::string line = content.substr(pos, nl - pos);
    pos = nl + 1;
    int tri;
    std::string path;
    JournalRecord rec;
    if (!ParseJournalLine(line, &tri, &path, &rec)) { bad++; continue; }
    // First record wins; a node is only decided once.
    m.emplace(std::make_pair(tri, path), rec);
  }
  if (bad) {
    std::cerr << "[journal] " << filename << ": ignored " << bad << " malformed/truncated lines\n";
  }
  return m;
}

// Import from an existing tree.X.json: keep splits and Tag 1 leaves.
static void ImportTreeNode(int tri, const TreeNode &node, const std::string &path,
                           JournalMap *m, int *leaves, int *dropped) {
  if (!node.children.empty()) {
    (*m)[{tri, path}].is_split = true;
    for (int c = 0; c < (int)node.children.size(); c++) {
      if (node.children[c])
        ImportTreeNode(tri, *node.children[c], path + (char)('0' + c), m, leaves, dropped);
    }
  } else if (node.direct_cert.has_value()) {
    JournalRecord rec;
    rec.cert = node.direct_cert.value();
    (*m)[{tri, path}] = rec;
    (*leaves)++;
  } else {
    (*dropped)++;
  }
}

// ---------------- Solver ----------------

struct WorkItem {
  int tri = 0;
  std::string path;
  TriangleQ triangle;
  std::optional<LocalCertificate> hint;
  // Number of consecutive ancestors that skipped the fresh cage search.
  int skips = 0;
};

class CodeSolver {
 public:
  CodeSolver(int code_idx, const rapidjson::Value &code_obj, const SolverOptions &opt)
      : code_idx_(code_idx), opt_(opt) {
    code_hex_ = code_obj["code_hex"].GetString();
    const auto &tri_arr = code_obj["triangles"].GetArray();
    for (rapidjson::SizeType t = 0; t < tri_arr.Size(); t++) {
      TriangleQ tq;
      for (int k = 0; k < 3; k++) {
        tq.corners[k] = BigVecQ3(tri_arr[t][k]["x"].GetString(),
                                 tri_arr[t][k]["y"].GetString(),
                                 tri_arr[t][k]["z"].GetString());
      }
      roots_.push_back(tq);
    }
    journal_path_ = StringPrintf("%s/code.%d.journal", opt.output_dir.c_str(), code_idx);
    tree_path_ = StringPrintf("%s/tree.%d.json", opt.output_dir.c_str(), code_idx);
  }

  // Returns true if every triangle of the code is fully certified.
  bool Run() {
    if (!opt_.force && !std::filesystem::exists(journal_path_) &&
        std::filesystem::exists(tree_path_)) {
      auto loaded = LoadCodeTreeJson(tree_path_);
      if (loaded && loaded->IsFullyCertified() && AllTag1(*loaded)) {
        printf("[Code %d] %s already fully certified with Tag 1 (%d leaves). Skipping.\n",
               code_idx_, tree_path_.c_str(), loaded->TotalLeaves());
        return true;
      }
      if (loaded && opt_.import_tree) {
        JournalMap m;
        int leaves = 0, dropped = 0;
        for (const auto &ct : loaded->triangles) {
          if (ct.root) ImportTreeNode(ct.triangle_index, *ct.root, "", &m, &leaves, &dropped);
        }
        std::string s;
        for (const auto &[key, rec] : m) {
          if (rec.is_split) s += StringPrintf("S %d %s\n", key.first, PathToken(key.second).c_str());
          else s += LeafLine(key.first, key.second, rec.cert);
        }
        CHECK(Util::WriteFile(journal_path_, s));
        printf("[Code %d] Imported %d Tag 1 leaves from %s (%d other leaves left pending).\n",
               code_idx_, leaves, tree_path_.c_str(), dropped);
      }
    }
    if (opt_.force && std::filesystem::exists(journal_path_)) {
      std::filesystem::rename(journal_path_, journal_path_ + ".old");
    }

    journal_ = ReadJournal(journal_path_);
    std::vector<WorkItem> replay_leaves;
    for (int t = 0; t < (int)roots_.size(); t++) {
      if (opt_.tri_id >= 0 && t != opt_.tri_id) continue;
      Replay(t, "", roots_[t], &replay_leaves);
    }
    int replayed = AuditReplayedLeaves(&replay_leaves);
    printf("[Code %d] Replayed %d journal leaves; %zu pending nodes.\n",
           code_idx_, replayed, queue_.size());
    fflush(stdout);

    journal_out_ = fopen(journal_path_.c_str(), "ab");
    CHECK(journal_out_ != nullptr) << journal_path_;

    auto start = std::chrono::steady_clock::now();
    std::vector<std::thread> threads;
    for (int i = 0; i < opt_.num_threads; i++) {
      threads.emplace_back([this, i]() { Worker(i); });
    }
    std::thread status([this, start]() { StatusLoop(start); });
    for (auto &th : threads) th.join();
    {
      std::lock_guard<std::mutex> l(mu_);
      done_ = true;
    }
    status_cv_.notify_all();
    status.join();
    fclose(journal_out_);
    journal_out_ = nullptr;

    printf("[Code %d] Finished: %lld new leaves, %lld new splits, %lld failures.\n",
           code_idx_, (long long)new_leaves_.load(), (long long)new_splits_.load(),
           (long long)failures_.load());
    if (failures_.load() > 0) return false;
    if (opt_.tri_id >= 0) {
      printf("[Code %d] Only triangle %d was solved; not writing %s.\n",
             code_idx_, opt_.tri_id, tree_path_.c_str());
      return true;
    }
    return WriteTree();
  }

 private:
  static bool AllTag1(const CodeTree &ct) {
    std::function<bool(const TreeNode &)> rec = [&](const TreeNode &n) {
      if (!n.children.empty()) {
        for (const auto &c : n.children) if (!c || !rec(*c)) return false;
        return true;
      }
      return n.direct_cert.has_value() && !n.decomposed_cert.has_value();
    };
    for (const auto &t : ct.triangles) if (!t.root || !rec(*t.root)) return false;
    return true;
  }

  // Walk the journal from a node; queue pending nodes and collect the
  // journal leaves, which are re-audited (in parallel) before being
  // trusted.
  void Replay(int tri, const std::string &path, const TriangleQ &triangle,
              std::vector<WorkItem> *leaves) {
    auto it = journal_.find({tri, path});
    if (it == journal_.end()) {
      queue_.push_back({tri, path, triangle, std::nullopt});
      return;
    }
    if (it->second.is_split) {
      TriangleQ ch[4];
      triangle.Subdivide(ch);
      for (int c = 0; c < 4; c++) Replay(tri, path + (char)('0' + c), ch[c], leaves);
      return;
    }
    leaves->push_back({tri, path, triangle, it->second.cert});
  }

  // Re-audit journal leaves; failures go back to the queue (with their
  // contacts as a hint).
  int AuditReplayedLeaves(std::vector<WorkItem> *leaves) {
    std::atomic<size_t> next{0};
    std::atomic<int> good{0};
    std::vector<std::thread> threads;
    for (int i = 0; i < opt_.num_threads; i++) {
      threads.emplace_back([&]() {
        for (;;) {
          size_t idx = next.fetch_add(1);
          if (idx >= leaves->size()) return;
          WorkItem &item = (*leaves)[idx];
          LocalCertificate audited;
          std::string why;
          bool ok = ReauditCertificate(item.triangle, *item.hint, opt_.target_c,
                                       opt_.target_r, &audited, &why);
          std::lock_guard<std::mutex> l(mu_);
          if (ok) {
            audited_[{item.tri, item.path}] = audited;
            good++;
          } else {
            fprintf(stderr, "[Code %d] journal leaf tri %d path %s failed re-audit (%s); requeued\n",
                    code_idx_, item.tri, PathToken(item.path).c_str(), why.c_str());
            journal_.erase({item.tri, item.path});
            queue_.push_back(item);
          }
        }
      });
    }
    for (auto &th : threads) th.join();
    return good.load();
  }

  void Append(const std::string &line) {
    // Called with mu_ held.
    fwrite(line.data(), 1, line.size(), journal_out_);
    fflush(journal_out_);
  }

  bool TryCertify(const WorkItem &item, unsigned int *seed, LocalCertificate *out,
                  std::optional<LocalCertificate> *next_hint, bool *skip_search) {
    const int depth = item.path.size();
    std::string why;
    *skip_search = false;
    if (item.hint.has_value()) {
      BigRat cover(-1), delta(-1);
      if (ReauditCertificate(item.triangle, *item.hint, opt_.target_c, opt_.target_r, out, &why,
                             &cover, &delta))
        return true;
      // If the parent's cage fails only because the variation delta is a
      // bit too large, one or two more splits (which roughly halve delta)
      // will fix it; skip the (expensive) fresh search. Never skip more
      // than twice in a row, since a cage with tiny cover never recovers.
      if (depth > 6 && item.skips < 2 && why.rfind("cover <= delta", 0) == 0 &&
          cover > BigRat(0) && cover * BigRat(4) >= delta) {
        *skip_search = true;
        return false;
      }
    }

    LocalCertificate local;
    double margin = 0;
    bool has_local = FindBestCageForTriangle(item.triangle, seed, &local, &margin);
    if (!has_local) {
      has_local = SynthesizeCertificate(item.triangle, depth, opt_.target_c, opt_.target_r,
                                        &local, false);
    }
    if (has_local) {
      if (ReauditCertificate(item.triangle, local, opt_.target_c, opt_.target_r, out, &why))
        return true;
      *next_hint = local;
    }
    return false;
  }

  void Worker(int thread_idx) {
    for (;;) {
      WorkItem item;
      {
        std::unique_lock<std::mutex> l(mu_);
        cv_.wait(l, [this]() { return !queue_.empty() || active_ == 0; });
        if (queue_.empty()) {
          cv_.notify_all();
          return;
        }
        // LIFO keeps the frontier small (depth-first).
        item = std::move(queue_.back());
        queue_.pop_back();
        active_++;
      }

      unsigned int seed = 42 + 1000 * code_idx_ + 7919 * item.tri;
      for (char c : item.path) seed = seed * 31 + c;

      LocalCertificate audited;
      std::optional<LocalCertificate> next_hint = item.hint;
      bool skipped = false;
      bool ok = TryCertify(item, &seed, &audited, &next_hint, &skipped);
      const int depth = item.path.size();

      std::vector<WorkItem> children;
      {
        std::lock_guard<std::mutex> l(mu_);
        if (ok) {
          Append(LeafLine(item.tri, item.path, audited));
          journal_[{item.tri, item.path}].cert = audited;
          audited_[{item.tri, item.path}] = audited;
          new_leaves_++;
          min_c_ = min_c_ == 0 ? audited.c.ToDouble() : std::min(min_c_, audited.c.ToDouble());
        } else if (depth >= opt_.max_depth) {
          failures_++;
          fprintf(stderr, "[Code %d] FAILED tri %d path %s at max depth %d\n",
                  code_idx_, item.tri, item.path.c_str(), depth);
        } else {
          Append(StringPrintf("S %d %s\n", item.tri, PathToken(item.path).c_str()));
          journal_[{item.tri, item.path}].is_split = true;
          new_splits_++;
          max_depth_seen_ = std::max(max_depth_seen_, depth + 1);
          TriangleQ ch[4];
          item.triangle.Subdivide(ch);
          // Push in reverse so child 0 is processed first.
          for (int c = 3; c >= 0; c--) {
            queue_.push_back({item.tri, item.path + (char)('0' + c), ch[c], next_hint,
                              skipped ? item.skips + 1 : 0});
          }
        }
        active_--;
      }
      cv_.notify_all();
    }
  }

  void StatusLoop(std::chrono::steady_clock::time_point start) {
    std::unique_lock<std::mutex> l(mu_);
    auto next_report = std::chrono::steady_clock::now() + std::chrono::seconds(60);
    while (!done_) {
      status_cv_.wait_until(l, next_report);
      if (done_) break;
      if (std::chrono::steady_clock::now() < next_report) continue;
      next_report += std::chrono::seconds(60);
      double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
      printf("[Code %d %.0fs] leaves +%lld, splits +%lld, pending %zu, active %d, max depth %d, min c %.3g, failures %lld\n",
             code_idx_, secs, (long long)new_leaves_.load(), (long long)new_splits_.load(),
             queue_.size(), active_, max_depth_seen_, min_c_, (long long)failures_.load());
      fflush(stdout);
    }
  }

  // Build the full tree from the (audited) journal records and save.
  bool WriteTree() {
    const JournalMap &m = journal_;
    CodeTree code_tree;
    code_tree.code_id = code_idx_;
    code_tree.code_hex = code_hex_;
    int total = 0;
    for (int t = 0; t < (int)roots_.size(); t++) {
      CodeTriangleTree ct;
      ct.triangle_index = t;
      ct.triangle = roots_[t];
      ct.root = Build(m, t, "", roots_[t], &total);
      if (!ct.root) {
        fprintf(stderr, "[Code %d] Triangle %d incomplete; not writing tree.\n", code_idx_, t);
        return false;
      }
      code_tree.triangles.push_back(std::move(ct));
    }
    CHECK(code_tree.IsFullyCertified());
    if (!SaveCodeTreeJson(code_tree, tree_path_)) {
      fprintf(stderr, "[Code %d] Failed to save %s\n", code_idx_, tree_path_.c_str());
      return false;
    }
    printf("[Code %d] SUCCESS: %d Tag 1 leaves across %zu triangles -> %s\n",
           code_idx_, total, roots_.size(), tree_path_.c_str());
    return true;
  }

  std::unique_ptr<TreeNode> Build(const JournalMap &m, int tri, const std::string &path,
                                  const TriangleQ &triangle, int *total) {
    auto it = m.find({tri, path});
    if (it == m.end()) return nullptr;
    auto node = std::make_unique<TreeNode>();
    node->path = path;
    node->explicit_triangle = triangle;
    if (it->second.is_split) {
      TriangleQ ch[4];
      triangle.Subdivide(ch);
      node->children.resize(4);
      for (int c = 0; c < 4; c++) {
        node->children[c] = Build(m, tri, path + (char)('0' + c), ch[c], total);
        if (!node->children[c]) return nullptr;
      }
      return node;
    }
    auto ait = audited_.find({tri, path});
    if (ait == audited_.end()) return nullptr;
    const LocalCertificate &audited = ait->second;
    node->direct_cert = audited;
    node->direct_bounds.direct_r_lower = audited.r;
    node->direct_bounds.direct_c_lower = audited.c;
    (*total)++;
    return node;
  }

  const int code_idx_;
  const SolverOptions opt_;
  std::string code_hex_;
  std::vector<TriangleQ> roots_;
  std::string journal_path_, tree_path_;
  JournalMap journal_;
  FILE *journal_out_ = nullptr;

  std::mutex mu_;
  std::condition_variable cv_, status_cv_;
  std::map<std::pair<int, std::string>, LocalCertificate> audited_;
  std::vector<WorkItem> queue_;
  int active_ = 0;
  bool done_ = false;
  int max_depth_seen_ = 0;
  double min_c_ = 0;
  std::atomic<int64_t> new_leaves_{0}, new_splits_{0}, failures_{0};
};

#ifndef TUBECODE_NO_MAIN
int main(int argc, char **argv) {
  SolverOptions opt;
  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--code" && i + 1 < argc) {
      opt.code_id = std::stoi(argv[++i]);
    } else if (arg == "--tri" && i + 1 < argc) {
      opt.tri_id = std::stoi(argv[++i]);
    } else if (arg == "--threads" && i + 1 < argc) {
      opt.num_threads = std::stoi(argv[++i]);
    } else if (arg == "--max_depth" && i + 1 < argc) {
      opt.max_depth = std::stoi(argv[++i]);
    } else if (arg == "--output_dir" && i + 1 < argc) {
      opt.output_dir = argv[++i];
    } else if (arg == "--force") {
      opt.force = true;
    } else if (arg == "--import") {
      opt.import_tree = true;
    } else {
      fprintf(stderr, "Unknown argument %s\n"
              "Usage: tubecode229.exe [--code X [--tri T]] [--threads N] [--max_depth D]\n"
              "                       [--output_dir DIR] [--force] [--import]\n", arg.c_str());
      return 2;
    }
  }

  std::filesystem::create_directories(opt.output_dir);

  std::string bdd_content = Util::ReadFile(opt.bdd_json);
  rapidjson::Document doc;
  doc.Parse(bdd_content.c_str());
  CHECK(!doc.HasParseError() && doc.HasMember("codes"));

  const auto &codes = doc["codes"].GetArray();
  int num_codes = static_cast<int>(codes.Size());

  std::vector<int> todo;
  if (opt.code_id >= 0) {
    if (opt.code_id >= num_codes) {
      std::cerr << "Invalid code id " << opt.code_id << " (total " << num_codes << ")\n";
      return 1;
    }
    todo.push_back(opt.code_id);
  } else {
    for (int c = 0; c < num_codes; c++) todo.push_back(c);
  }

  // Codes are solved one at a time, each using all worker threads.
  int ok = 0, failed = 0;
  for (int c : todo) {
    CodeSolver solver(c, codes[c], opt);
    if (solver.Run()) ok++;
    else failed++;
  }
  printf("Synthesis finished: %d/%zu codes complete, %d incomplete.\n", ok, todo.size(), failed);
  return failed == 0 ? 0 : 1;
}
#endif
