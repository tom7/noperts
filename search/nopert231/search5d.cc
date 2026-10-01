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
//                [--charts 0,1,2] [--threads N] [--commit_depth D]
//                [--subtree_budget N] [--out_dir jobs] [--trees_dir trees_r1]
//                [--bdd codebdd229.json] [--cone_samples N] [--split_kappa K]
//                [--exact_check] [--retry_deferred]
//
// --retry_deferred also solves every deferred (df) leaf in the journals again
// (typically with a larger --subtree_budget); its new records replace it.

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
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"
#include "rows5d.h"
#include "solve5d.h"
#include "tubeatlas5d.h"
#include "util.h"

namespace {

struct Args {
  std::vector<int> triangles;
  std::vector<int> charts = {0, 1, 2};
  int threads = 0;
  int commit_depth = 6;
  int64_t subtree_budget = 200000;
  std::string out_dir = "jobs";
  std::string trees_dir = "trees_r1";
  std::string bdd = "codebdd229.json";
  bool retry_deferred = false;
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
  solve5d::Solver solver(&atlas, state->job, args.opt);
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
    else if (a == "--max_depth") args.opt.max_depth = std::stoi(next());
    else if (a == "--exact_check") args.opt.exact_check = true;
    else if (a == "--retry_deferred") args.retry_deferred = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  if (args.threads <= 0) args.threads = std::max(1u, std::thread::hardware_concurrency());

  const auto atlas = tubeatlas5d::TubeAtlas::Load(args.trees_dir, args.bdd);
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
    CHECK(chart >= 0 && chart <= 2) << "chart 3 is a fixed table in Lean";
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

  std::atomic<size_t> next{0};
  std::mutex stats_mu;
  solve5d::Stats total;
  size_t finished = 0;
  const auto start = std::chrono::steady_clock::now();
  auto worker = [&]() {
    for (;;) {
      const size_t i = next.fetch_add(1);
      if (i >= items.size()) return;
      WorkItem &item = items[i];
      solve5d::Solver solver(&atlas, item.state->job, args.opt);
      const auto records = solver.SolveSubtree(item.node, args.subtree_budget);
      item.state->Append(records, item.node.path);
      std::lock_guard<std::mutex> l(stats_mu);
      total.Add(solver.stats());
      finished++;
      if (finished % 64 == 0 || finished == items.size()) {
        const double sec =
            std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        printf("[%zu/%zu subtrees, %.0fs] nodes %lld (%.0f/s): ce %lld tu %lld pr %lld pf %lld "
               "df %lld\n",
               finished, items.size(), sec, (long long)total.nodes, total.nodes / std::max(sec, 1e-9),
               (long long)total.ce, (long long)total.tu, (long long)total.pr, (long long)total.pf,
               (long long)total.df);
        fflush(stdout);
      }
    }
  };
  std::vector<std::thread> pool;
  for (int k = 0; k < args.threads; k++) pool.emplace_back(worker);
  for (auto &th : pool) th.join();
  printf("Finished: %lld nodes, %lld deferred leaves%s\n", (long long)total.nodes,
         (long long)total.df, total.df ? " (rerun with a larger --subtree_budget to retry)" : "");
  return 0;
}
