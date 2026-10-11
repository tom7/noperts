// capleaf_check: re-checks every cap leaf (cl) of the 5D journals exactly
// (exact5d::CapLeafValid, the exact frame of the caps file: the Septopert's
// rebuild.sh or the DH's dh_caps.py writes it). The
// search does this when it creates a cap leaf; this covers journals written
// by searches that screened cap leaves in double precision only.
//
// Usage: capleaf_check.exe --caps caps.txt [--jobs DIR] [--trees_dir DIR] [--bdd codebdd.json]
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include "base/logging.h"
#include "geom5d.h"
#include "rows5d.h"
#include "tubeatlas5d.h"
int main(int argc, char **argv) {
  std::string jobs = "jobs", trees = "trees_r2", bdd = "codebdd.json", caps_file;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--caps") caps_file = next();
    else if (a == "--jobs") jobs = next();
    else if (a == "--trees_dir") trees = next();
    else if (a == "--bdd") bdd = next();
    else LOG(FATAL) << "unknown argument " << a;
  }
  std::vector<exact5d::CapExact> caps;
  {
    std::ifstream in(caps_file);
    CHECK(in.good()) << caps_file;
    std::string line;
    while (std::getline(in, line)) {
      std::istringstream ss(line);
      std::string t[49];
      for (auto &tok : t) CHECK(ss >> tok) << line;
      exact5d::CapExact c;
      for (int f = 0; f < 3; f++)
        for (int a = 0; a < 3; a++) {
          const std::string *q = &t[11 + 4 * (3 * f + a)];
          c.frame[f][a] = {BigRat(std::string_view(q[0])), BigRat(std::string_view(q[1])),
                           BigRat(std::string_view(q[2])), BigRat(std::string_view(q[3]))};
        }
      c.mu0 = BigRat(std::string_view(t[47]));
      c.wmax2 = BigRat(std::string_view(t[48]));
      caps.push_back(c);
    }
  }
  auto atlas = tubeatlas5d::TubeAtlas::Load(trees, bdd);
  int64_t total = 0, bad = 0;
  for (int chart = 0; chart < 4; chart++) {
    const std::string dir = jobs + "/c" + std::to_string(chart);
    if (!std::filesystem::exists(dir)) continue;
    for (const auto &ent : std::filesystem::directory_iterator(dir)) {
      const std::string name = ent.path().filename().string();
      if (name.size() < 10 || name[0] != 't' || !name.ends_with(".journal")) continue;
      const int t = std::stoi(name.substr(1));
      const auto j = rows5d::ReadJournal(ent.path().string());
      for (const auto &r : j.leaves) {
        const auto *cl = std::get_if<rows5d::CapLeaf>(&r.leaf);
        if (cl == nullptr) continue;
        total++;
        CHECK(cl->cap >= 0 && cl->cap < (int)caps.size()) << r.path;
        const auto T = rows5d::NodeTriangle(atlas.Triangle(t), r.path);
        const auto B = rows5d::NodeBox(geom5d::RootBox(chart), r.path);
        if (!exact5d::CapLeafValid(geom5d::ToInterval(B), T, chart, caps[cl->cap])) {
          bad++;
          printf("INVALID c%d t%d %s cap %d\n", chart, t, r.path.c_str(), cl->cap);
        }
      }
    }
  }
  printf("%lld cap leaves, %lld invalid\n", (long long)total, (long long)bad);
  return bad == 0 ? 0 : 1;
}
