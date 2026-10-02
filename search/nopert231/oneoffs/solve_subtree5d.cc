// Solves given 5D subtrees from scratch with a chosen split rule and reports
// node and leaf counts (for comparing split rules on heavy subtrees).
//
// Usage: solve_subtree5d.exe <t> <chart> <view_scale> <split_rule> <budget> <path>...

#include <chrono>
#include <cstdio>
#include <string>
#include <thread>
#include <vector>

#include "rows5d.h"
#include "solve5d.h"
#include "tubeatlas5d.h"

int main(int argc, char **argv) {
  const int t = std::stoi(argv[1]), chart = std::stoi(argv[2]);
  solve5d::Options opt;
  opt.view_scale = std::stod(argv[3]);
  // split_rule 10 + r: rule r with view_lookahead.
  opt.split_rule = std::stoi(argv[4]) % 10;
  opt.view_lookahead = std::stoi(argv[4]) >= 10;
  opt.max_depth = 200;
  const long long budget = std::stoll(argv[5]);
  const auto atlas = tubeatlas5d::TubeAtlas::Load("trees_r2", "codebdd231.json");
  const auto root = solve5d::RootNode(atlas, {.t = t, .chart = chart});
  std::vector<std::string> paths(argv + 6, argv + argc);
  std::vector<std::string> out(paths.size());
  std::vector<std::thread> threads;
  for (size_t i = 0; i < paths.size(); i++) {
    threads.emplace_back([&, i]() {
      const auto start = std::chrono::steady_clock::now();
      solve5d::Solver solver(&atlas, {.t = t, .chart = chart}, opt);
      solve5d::Node node{.path = paths[i], .tri = rows5d::NodeTriangle(root.tri, paths[i]),
                         .box = rows5d::NodeBox(root.box, paths[i])};
      solver.SolveSubtree(node, budget);
      const auto &s = solver.stats();
      const double sec =
          std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
      char buf[512];
      snprintf(buf, sizeof(buf), "%s: nodes %lld leaves %lld (ce %lld mx %lld tu %lld df %lld) %.0fs",
               paths[i].c_str(), (long long)s.nodes,
               (long long)(s.ce + s.mx + s.tu + s.pr + s.pf + s.df), (long long)s.ce, (long long)s.mx,
               (long long)s.tu, (long long)s.df, sec);
      out[i] = buf;
    });
  }
  for (auto &th : threads) th.join();
  for (const auto &l : out) printf("%s\n", l.c_str());
  return 0;
}
