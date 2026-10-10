// tufix: defer the identity-tube leaves ("tu <path> <r>") of a 5D job journal
// whose radius exceeds the tube atlas's bound at their view node (e.g. after the
// atlas stopped crediting tube-tree cap leaves with a radius), so that
// search5d --retry_deferred re-solves them. Rewrites the journal in place
// (keeping <journal>.orig) and prints the number of leaves deferred.
//
// Usage: tufix.exe --t T --journal FILE [--trees_dir DIR] [--bdd codebdd.json]

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "rows5d.h"
#include "tubeatlas5d.h"

int main(int argc, char **argv) {
  std::string journal, trees = "trees_r3", bdd = "codebdd.json";
  int t = -1;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--t") t = std::stoi(next());
    else if (a == "--journal") journal = next();
    else if (a == "--trees_dir") trees = next();
    else if (a == "--bdd") bdd = next();
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(t >= 0 && !journal.empty());
  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees, bdd);
  std::ifstream in(journal);
  CHECK(in.good()) << journal;
  std::vector<std::string> lines;
  std::string line;
  int64_t deferred = 0, kept = 0;
  while (std::getline(in, line)) {
    if (line.rfind("tu ", 0) == 0) {
      std::istringstream ss(line);
      std::string tag, path, r;
      ss >> tag >> path >> r;
      const std::string vp = rows5d::ViewPath(path == "." ? "" : path);
      const BigRat bound = atlas.Walk(t, vp).r_lower;
      if (bound < BigRat(std::string_view(r))) {
        lines.push_back("df " + path);
        deferred++;
        continue;
      }
      kept++;
    }
    lines.push_back(line);
  }
  in.close();
  if (deferred > 0) {
    std::rename(journal.c_str(), (journal + ".orig").c_str());
    std::ofstream out(journal);
    for (const auto &l : lines) out << l << "\n";
  }
  printf("%s: %lld tube leaves deferred, %lld kept\n", journal.c_str(), (long long)deferred, (long long)kept);
  return 0;
}
