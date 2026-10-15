// Generated data that some unit tests need and the repository does not
// commit: codebdd.json, written by the solid's model stage. Without it those
// tests (or their parts that need it) print SKIPPED and pass, so that `make
// test` works in a fresh clone.
#ifndef _NOPERT_TEST_DATA_H
#define _NOPERT_TEST_DATA_H

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <string>

// codebdd's output: ./codebdd.json, or $CODEBDD_JSON.
inline std::string CodebddJson() {
  const char *e = getenv("CODEBDD_JSON");
  return e != nullptr ? e : "codebdd.json";
}

// Whether codebdd.json is there; if not, prints why `what` is skipped.
inline bool HaveCodebddJson(const char *what) {
  if (std::filesystem::exists(CodebddJson())) return true;
  printf("SKIPPED %s: %s not found; run the model stage first (rebuild.sh --only model)\n", what,
         CodebddJson().c_str());
  return false;
}

#endif
