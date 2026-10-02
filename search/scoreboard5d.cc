// Status of the 5D search per job (code triangle t, chart), from the
// journals: leaves by kind, deferred leaves, deepest node, and whether the
// job's tree is complete (packable: a complete tree with no deferred leaves).
//
// A packable job is also "packed" when its per-code pack (pack5d --per_code)
// is newer than its journal, and "checked" when Lean's check_global_rows
// passed on that pack (its .checked file is newer than the pack).
//
// Usage: scoreboard5d.exe [--journals jobs] [--packs packs] [--charts 0,1,2]
//                         [--bdd codebdd231.json]
//                         [--all]   (also list jobs with no journal yet)

#include <cstdio>
#include <filesystem>
#include <format>
#include <string>
#include <variant>
#include <vector>

#include "base/logging.h"
#include "rapidjson/document.h"
#include "rows5d.h"
#include "util.h"

int main(int argc, char **argv) {
  std::string journals = "jobs", packs = "packs", bdd = "codebdd231.json";
  std::vector<int> charts = {0, 1, 2};
  bool list_all = false;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--journals") journals = next();
    else if (a == "--packs") packs = next();
    else if (a == "--bdd") bdd = next();
    else if (a == "--all") list_all = true;
    else if (a == "--charts") {
      charts.clear();
      for (const auto &tok : Util::Split(next(), ',')) charts.push_back(std::stoi(tok));
    } else LOG(FATAL) << "unknown argument " << a;
  }
  // A wrong --journals directory would otherwise just show nothing started.
  CHECK(std::filesystem::is_directory(journals))
      << "no journal directory " << journals << " (pass --journals DIR)";
  rapidjson::Document doc;
  doc.Parse(Util::ReadFile(bdd).c_str());
  CHECK(!doc.HasParseError());
  std::vector<std::pair<int, int>> code_tri;  // t -> (code, tri)
  for (rapidjson::SizeType c = 0; c < doc["codes"].Size(); c++) {
    for (rapidjson::SizeType k = 0; k < doc["codes"][c]["triangles"].Size(); k++) {
      code_tri.push_back({(int)c, (int)k});
    }
  }

  printf("%-5s %-4s %-9s %9s %9s %8s %8s %8s %7s %5s  %s\n", "chart", "t", "code.tri", "leaves",
         "ce+mx", "tu", "pr", "pf", "df", "depth", "status");
  int packable = 0, started = 0, jobs = 0, packed = 0, checked_count = 0;
  for (int chart : charts) {
    for (int t = 0; t < (int)code_tri.size(); t++) {
      jobs++;
      const std::string path = std::format("{}/c{}/t{}.journal", journals, chart, t);
      if (!std::filesystem::exists(path)) {
        if (list_all) {
          printf("%-5d %-4d %4d.%-4d %9s %9s %8s %8s %8s %7s %5s  not started\n", chart, t,
                 code_tri[t].first, code_tri[t].second, "-", "-", "-", "-", "-", "-", "-");
        }
        continue;
      }
      started++;
      const rows5d::Journal j = rows5d::ReadJournal(path);
      int64_t ce = 0, tu = 0, pr = 0, pf = 0, df = 0;
      size_t depth = 0;
      for (const auto &r : j.leaves) {
        depth = std::max(depth, r.path.size());
        std::visit(
            [&](const auto &l) {
              using T = std::decay_t<decltype(l)>;
              if constexpr (std::is_same_v<T, rows5d::CertLeaf> ||
                            std::is_same_v<T, rows5d::MixedLeaf>) ce++;
              else if constexpr (std::is_same_v<T, rows5d::TubeLeaf>) tu++;
              else if constexpr (std::is_same_v<T, rows5d::RadiusPruneLeaf>) pr++;
              else if constexpr (std::is_same_v<T, rows5d::FundamentalPruneLeaf>) pf++;
              else df++;
            },
            r.leaf);
      }
      const bool complete = std::holds_alternative<rows5d::Tree>(rows5d::BuildTree(j.leaves));
      const char *status = !complete ? "incomplete" : df ? "deferred leaves" : "PACKABLE";
      packable += complete && !df;
      if (complete && !df) {
        namespace fs = std::filesystem;
        const fs::path pack = std::format("{}/c{}/t{}.pack", packs, chart, t);
        const fs::path checked = std::format("{}/c{}/t{}.pack.checked", packs, chart, t);
        if (fs::exists(pack) && fs::last_write_time(pack) > fs::last_write_time(path)) {
          status = "PACKED";
          packed++;
          if (fs::exists(checked) && fs::last_write_time(checked) > fs::last_write_time(pack)) {
            status = "CHECKED";
            checked_count++;
          }
        }
      }
      printf("%-5d %-4d %4d.%-4d %9zu %9lld %8lld %8lld %8lld %7lld %5zu  %s\n", chart, t,
             code_tri[t].first, code_tri[t].second, j.leaves.size(), (long long)ce, (long long)tu,
             (long long)pr, (long long)pf, (long long)df, depth, status);
    }
  }
  printf("%d of %d jobs started, %d packable, %d packed, %d checked\n", started, jobs, packable,
         packed, checked_count);
  return 0;
}
