// The 5D search driver. For each job (code triangle t, chart), the top of
// the tree is expanded deterministically to --commit_depth using only the
// cheap exact leaves (prunes, tube); the nodes at that depth are solved in
// parallel (solve5d), and each finished subtree is appended to the job's
// journal (jobs/c<chart>/t<t>.journal) followed by "done <path>". Restarting
// skips subtrees already done, so work is never lost beyond the subtrees in
// flight, and failed deep subdivisions never reach disk: a subtree over its
// node budget ends in deferred (df) leaves instead (see rows5d, solve5d).
//
// Usage:
//   search5d.exe --t <triangle>[,<triangle>...] | --code <code> | --all
//                [--charts 0,1,2(,3)] [--threads N] [--commit_depth D]
//                [--subtree_budget N] [--out_dir jobs] [--trees_dir trees_r2]
//                [--bdd codebdd.json] [--cone_samples N] [--split_kappa K]
//                [--split_rule 0|1|2] [--min_peel 5..7]
//                [--view_scale S] [--view_lookahead] [--lookahead_band B] [--tube_view_depth D]
//                [--max_full_retry N] [--half_turn_prune] [--tie_dir DIR] [--caps FILE] [--trib_caps FILE]
//                [--exact_check] [--retry_deferred] [--requeue_deferred] [--blend5d L]
//
// --blend5d L (default 4, validated on the Septopert and the snub
// dodecahedron): 0 the inner vertex per contact at the box centre (the
// earlier behavior); 1 box-aware; 2 box-aware with blended inner points
// (pack tags 17 / 18; a solid's Lean decoder must read them); 3 the
// portfolio (both 0 and 2 per box, the better kept); 4 escalate (0 first,
// 2 only where 0 fails, since blended rows cost more bytes). Septopert
// packs: 51.4 MB with 2, 46.4 MB with 4; snub dodecahedron: 96.6 / 99.7 /
// 97.8 / 96.4 MB for 0 / 2 / 3 / 4.
// (On the deltoidal hexecontahedron, 2 did not pay overall: per triangle
// the nodes drop a little, t22 34.4k / 32.4k / 31.3k for 0 / 2 / 3, but its
// huge contact pools make the box-aware choice costly per node.)
//
// --retry_deferred also solves every deferred (df) leaf in the journals again
// (typically with a larger --subtree_budget); its new records replace it.
// --requeue_deferred puts each solved subtree's deferred leaves back on the
// work queue in the same run, so the search goes on until nothing is
// deferred (except at --max_depth), without per-round restarts.

#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <filesystem>
#include <format>
#include <fstream>
#include <mutex>
#include <set>
#include <sstream>
#include <string>
#include <condition_variable>
#include <thread>
#include <vector>
#include <optional>

#include "solid.h"

#include "base/logging.h"
#include "rows5d.h"
#include "solve5d.h"
#include "tubeatlas5d.h"
#include "util.h"

namespace {

struct Args {
  std::vector<int> triangles;
  // Default: every chart, 0..solid::kMaxChart.
  std::vector<int> charts = [] {
    std::vector<int> c;
    for (int chart = 0; chart <= solid::kMaxChart; chart++) c.push_back(chart);
    return c;
  }();
  int threads = 0;
  int commit_depth = 6;
  int64_t subtree_budget = 200000;
  std::string out_dir = "jobs";
  std::string trees_dir = "trees_r2";
  std::string bdd = "codebdd.json";
  bool retry_deferred = false;
  bool requeue_deferred = false;
  std::string tie_dir;
  solve5d::Options opt;
};

std::vector<int> ParseInts(const std::string &s) {
  std::vector<int> out;
  for (const auto &tok : Util::Split(s, ',')) out.push_back(std::stoi(tok));
  return out;
}

std::string JournalPath(const Args &args, const solve5d::Job &job) {
  return std::format("{}/c{}/t{}.journal", args.out_dir, job.chart, job.t);
}

// One job's journal, appended to under a lock.
struct JobState {
  solve5d::Job job;
  std::string journal;
  std::set<std::string> done;  // completed subtree roots (from the journal)
  std::mutex mu;

  bool Covered(const std::string &path) const {
    for (size_t len = 0; len <= path.size(); len++) {
      if (done.count(path.substr(0, len))) return true;
    }
    return false;
  }

  void Append(const std::vector<rows5d::Record> &records, const std::string &root) {
    std::string text;
    for (const auto &r : records) text += rows5d::FormatRecord(r) + "\n";
    text += rows5d::FormatDone(root) + "\n";
    std::lock_guard<std::mutex> l(mu);
    std::ofstream f(journal, std::ios::app);
    CHECK(f.good()) << journal;
    f << text;
    f.flush();
    done.insert(root);
  }
};

struct WorkItem {
  JobState *state;
  solve5d::Node node;
};

// Expands the top of a job's tree; cheap leaves are journaled immediately,
// nodes at the commit depth become work items.
void ExpandTop(const tubeatlas5d::TubeAtlas &atlas, const Args &args, JobState *state,
               std::vector<WorkItem> *items) {
  // The top of the tree always uses the original split rule, so that
  // journals written with other rules below the commit depth stay valid.
  solve5d::Options top_opt = args.opt;
  top_opt.split_rule = 0;
  top_opt.view_scale = 0.0;
  top_opt.tube_view_depth = -1;
  top_opt.view_lookahead = false;
  solve5d::Solver solver(&atlas, state->job, top_opt);
  std::vector<solve5d::Node> stack = {solve5d::RootNode(atlas, state->job)};
  while (!stack.empty()) {
    solve5d::Node node = std::move(stack.back());
    stack.pop_back();
    if (state->Covered(node.path)) continue;
    if (auto leaf = solver.TryPrune(node)) {
      state->Append({{node.path, *leaf}}, node.path);
      continue;
    }
    if ((int)node.path.size() >= args.commit_depth) {
      items->push_back({state, std::move(node)});
      continue;
    }
    auto children = solve5d::Children(node, solver.ChooseSplit(node));
    for (auto it = children.rbegin(); it != children.rend(); ++it) stack.push_back(std::move(*it));
  }
}

}  // namespace

int main(int argc, char **argv) {
  Args args;
  cert5d::g_blend5d = 4;
  bool all = false;
  int code = -1;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--t") args.triangles = ParseInts(next());
    else if (a == "--code") code = std::stoi(next());
    else if (a == "--all") all = true;
    else if (a == "--charts") args.charts = ParseInts(next());
    else if (a == "--threads") args.threads = std::stoi(next());
    else if (a == "--commit_depth") args.commit_depth = std::stoi(next());
    else if (a == "--subtree_budget") args.subtree_budget = std::stoll(next());
    else if (a == "--out_dir") args.out_dir = next();
    else if (a == "--trees_dir") args.trees_dir = next();
    else if (a == "--bdd") args.bdd = next();
    else if (a == "--cone_samples") args.opt.cone_samples = std::stoi(next());
    else if (a == "--split_kappa") args.opt.split_kappa = std::stod(next());
    else if (a == "--split_rule") args.opt.split_rule = std::stoi(next());
    else if (a == "--view_scale") args.opt.view_scale = std::stod(next());
    else if (a == "--view_lookahead") args.opt.view_lookahead = true;
    else if (a == "--tube_view_depth") args.opt.tube_view_depth = std::stoi(next());
    else if (a == "--lookahead_band") args.opt.lookahead_band = std::stod(next());
    else if (a == "--max_full_retry") args.opt.max_full_retry = std::stoi(next());
    else if (a == "--half_turn_prune") args.opt.half_turn_prune = true;
    else if (a == "--tie_dir") args.tie_dir = next();
    else if (a == "--caps") {
      // dh_caps.py: 9 + 2 doubles, then the exact frame (36 rationals), mu0, wmax^2.
      std::ifstream in(next());
      std::string line;
      while (std::getline(in, line)) {
        std::istringstream ss(line);
        solve5d::Options::Cap c;
        CHECK(ss >> c.x[0] >> c.x[1] >> c.x[2] >> c.e1[0] >> c.e1[1] >> c.e1[2] >> c.e2[0] >> c.e2[1] >> c.e2[2] >>
              c.mu0 >> c.wmax) << line;
        std::string t[38];
        for (auto &tok : t) CHECK(ss >> tok) << "caps file without the exact frame: " << line;
        for (int f = 0; f < 3; f++)
          for (int a = 0; a < 3; a++) {
            const std::string *q = &t[4 * (3 * f + a)];
            c.exact.frame[f][a] = {BigRat(std::string_view(q[0])), BigRat(std::string_view(q[1])),
                                   BigRat(std::string_view(q[2])), BigRat(std::string_view(q[3]))};
          }
        c.exact.mu0 = BigRat(std::string_view(t[36]));
        c.exact.wmax2 = BigRat(std::string_view(t[37]));
        args.opt.caps.push_back(c);
      }
    }
    else if (a == "--trib_caps") {
      // Per line: kind mu0 R t0 s0, then x e1 e2 Z E1 X (each 3 coordinates
      // a b c = a + b t + c t^2). Rationals (sccapcert --caps).
      std::ifstream in(next());
      std::string line;
      while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::istringstream ss(line);
        exact5d::TribCap c;
        std::string tok[5];
        CHECK(ss >> c.kind >> tok[0] >> tok[1] >> tok[2] >> tok[3]) << line;
        c.mu0 = BigRat(std::string_view(tok[0]));
        c.R = BigRat(std::string_view(tok[1]));
        c.t0 = BigRat(std::string_view(tok[2]));
        c.s0 = BigRat(std::string_view(tok[3]));
        for (int f = 0; f < 6; f++)
          for (int i = 0; i < 3; i++) {
            std::string q[3];
            CHECK(ss >> q[0] >> q[1] >> q[2]) << line;
            c.frame[f][i] = {BigRat(std::string_view(q[0])), BigRat(std::string_view(q[1])),
                             BigRat(std::string_view(q[2]))};
          }
        args.opt.trib_caps.push_back(c);
      }
    }
    else if (a == "--min_peel") args.opt.min_peel_eighths = std::stoi(next());
    else if (a == "--max_depth") args.opt.max_depth = std::stoi(next());
    else if (a == "--exact_check") args.opt.exact_check = true;
    else if (a == "--blend5d") cert5d::g_blend5d = std::stoi(next());
    else if (a == "--max_mix") args.opt.max_mix_components = std::stoi(next());
    else if (a == "--retry_deferred") args.retry_deferred = true;
    else if (a == "--requeue_deferred") args.requeue_deferred = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  if (args.threads <= 0) args.threads = std::max(1u, std::thread::hardware_concurrency());

  const auto atlas = tubeatlas5d::TubeAtlas::Load(args.trees_dir, args.bdd);
  // Tie tubes (deltoidal hexecontahedron; tietube.cc output).
  std::optional<tieatlas5d::TieAtlas> ties;
  if (!args.tie_dir.empty()) {
    ties = tieatlas5d::TieAtlas::Load(args.tie_dir, solid::kTieHalfTurns.size, atlas.NumTriangles());
    args.opt.ties = &*ties;
  }
  if (all) {
    for (int t = 0; t < atlas.NumTriangles(); t++) args.triangles.push_back(t);
  } else if (code >= 0) {
    for (int t = 0; t < atlas.NumTriangles(); t++) {
      if (atlas.CodeAndTriangle(t).first == code) args.triangles.push_back(t);
    }
  }
  CHECK(!args.triangles.empty()) << "no jobs: use --t, --code or --all";

  // Jobs, their journals, and the work items.
  std::deque<JobState> states;
  std::vector<WorkItem> items;
  for (int chart : args.charts) {
    CHECK(chart >= 0 && chart <= solid::kMaxChart) << "chart " << chart << " (charts 0.." << solid::kMaxChart << ")";
    std::filesystem::create_directories(std::format("{}/c{}", args.out_dir, chart));
    for (int t : args.triangles) {
      JobState &s = states.emplace_back();
      s.job = {.t = t, .chart = chart};
      s.journal = JournalPath(args, s.job);
      const rows5d::Journal j = rows5d::ReadJournal(s.journal);
      s.done.insert(j.done.begin(), j.done.end());
      ExpandTop(atlas, args, &s, &items);
      if (args.retry_deferred) {
        const solve5d::Node root = solve5d::RootNode(atlas, s.job);
        for (const auto &r : j.leaves) {
          if (!std::holds_alternative<rows5d::DeferredLeaf>(r.leaf)) continue;
          items.push_back({&s, solve5d::Node{.path = r.path,
                                             .tri = rows5d::NodeTriangle(root.tri, r.path),
                                             .box = rows5d::NodeBox(root.box, r.path)}});
        }
      }
    }
  }
  printf("%zu jobs, %zu subtrees to solve on %d threads\n", states.size(), items.size(),
         args.threads);
  fflush(stdout);

  // The work queue. With --requeue_deferred, the deferred leaves of each
  // solved subtree go back on the queue at once (journaled like a
  // --retry_deferred round, without restarting the process).
  std::mutex queue_mu;
  std::condition_variable queue_cv;
  std::deque<WorkItem> queue(items.begin(), items.end());
  size_t in_flight = 0, queued_total = items.size();
  int64_t requeued = 0;
  solve5d::LiveCounters live;
  std::mutex stats_mu;
  solve5d::Stats total;
  size_t finished = 0;
  const auto start = std::chrono::steady_clock::now();
  auto worker = [&]() {
    for (;;) {
      WorkItem item;
      {
        std::unique_lock<std::mutex> l(queue_mu);
        queue_cv.wait(l, [&]() { return !queue.empty() || in_flight == 0; });
        if (queue.empty()) return;
        item = std::move(queue.front());
        queue.pop_front();
        in_flight++;
      }
      solve5d::Solver solver(&atlas, item.state->job, args.opt);
      solver.SetLive(&live);
      const auto records = solver.SolveSubtree(item.node, args.subtree_budget);
      item.state->Append(records, item.node.path);
      std::vector<WorkItem> more;
      if (args.requeue_deferred) {
        const solve5d::Node root = solve5d::RootNode(atlas, item.state->job);
        for (const auto &r : records) {
          if (!std::holds_alternative<rows5d::DeferredLeaf>(r.leaf)) continue;
          if ((int)r.path.size() > args.opt.max_depth) continue;
          more.push_back({item.state, solve5d::Node{.path = r.path,
                                                    .tri = rows5d::NodeTriangle(root.tri, r.path),
                                                    .box = rows5d::NodeBox(root.box, r.path)}});
        }
      }
      {
        std::lock_guard<std::mutex> l(queue_mu);
        for (auto &m : more) queue.push_back(std::move(m));
        queued_total += more.size();
        requeued += more.size();
        in_flight--;
      }
      queue_cv.notify_all();
      std::lock_guard<std::mutex> l(stats_mu);
      total.Add(solver.stats());
      finished++;
      if (finished % 64 == 0) {
        const double sec =
            std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        printf("[%zu/%zu subtrees, %.0fs] nodes %lld (%.0f/s): ce %lld mx %lld tu %lld pr %lld pf %lld "
               "df %lld (max pool %lld triples)\n",
               finished, queued_total, sec, (long long)total.nodes, total.nodes / std::max(sec, 1e-9),
               (long long)total.ce, (long long)total.mx, (long long)total.tu, (long long)total.pr, (long long)total.pf,
               (long long)total.df, (long long)total.max_pool_triples);
        fflush(stdout);
      }
    }
  };
  // A status line every minute, from the live counters (subtrees can run
  // for a long time before they are committed).
  std::mutex done_mu;
  std::condition_variable done_cv;
  bool done = false;
  std::thread status([&]() {
    std::unique_lock<std::mutex> l(done_mu);
    while (!done_cv.wait_for(l, std::chrono::seconds(60), [&]() { return done; })) {
      const double sec =
          std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
      printf("  [%.0fs] live: nodes %lld, leaves %lld (tu %lld), df %lld\n", sec,
             (long long)live.nodes.load(), (long long)live.leaves.load(),
             (long long)live.tu.load(), (long long)live.df.load());
      fflush(stdout);
    }
  });
  std::vector<std::thread> pool;
  for (int k = 0; k < args.threads; k++) pool.emplace_back(worker);
  for (auto &th : pool) th.join();
  {
    std::lock_guard<std::mutex> l(done_mu);
    done = true;
  }
  done_cv.notify_all();
  status.join();
  const int64_t left = total.df - requeued;
  printf("Finished: %lld nodes, %lld deferred leaves%s\n", (long long)total.nodes, (long long)left,
         left ? " (rerun with a larger --subtree_budget to retry)" : "");
  return 0;
}
