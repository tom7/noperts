// Probe: can pure Tag 1 certify sub-triangles of a code triangle that
// touch a given edge (e.g. the plane-6 edge of code 48 tri 1)?
// For each depth, samples random paths using only children 1 and 2
// (which preserve the corner1-corner2 edge) and reports the Tag 1 margin.
//
// Usage: probe48edge.exe [code] [tri] [max_depth] [samples_per_depth]

#include <map>
#define TUBECODE_NO_MAIN
#include "../tubecode229.cc"

int main(int argc, char **argv) {
  int code = argc > 1 ? atoi(argv[1]) : 48;
  int tri_idx = argc > 2 ? atoi(argv[2]) : 1;
  int max_depth = argc > 3 ? atoi(argv[3]) : 16;
  int samples = argc > 4 ? atoi(argv[4]) : 8;
  // Children digit alphabet; default keeps corner1-corner2 edge.
  std::string alphabet = argc > 5 ? argv[5] : "12";

  std::string bdd = Util::ReadFile("codebdd229.json");
  rapidjson::Document doc;
  doc.Parse(bdd.c_str());
  const auto &t = doc["codes"][code]["triangles"][tri_idx];
  TriangleQ root;
  for (int k = 0; k < 3; k++)
    root.corners[k] = BigVecQ3(t[k]["x"].GetString(), t[k]["y"].GetString(), t[k]["z"].GetString());

  std::mutex mu;
  std::vector<std::thread> threads;
  std::atomic<int> next{0};
  int total = (max_depth + 1) * samples;
  auto work = [&]() {
    for (;;) {
      int job = next.fetch_add(1);
      if (job >= total) return;
      int depth = job / samples;
      unsigned int seed = 1234 + job * 7919;
      std::string path;
      TriangleQ tri = root;
      bool fixed = alphabet[0] == 'P';
      if (fixed && depth >= (int)alphabet.size()) continue;
      for (int d = 0; d < depth; d++) {
        int digit = fixed ? alphabet[1 + d] - '0' : alphabet[rand_r(&seed) % alphabet.size()] - '0';
        TriangleQ ch[4];
        tri.Subdivide(ch);
        tri = ch[digit];
        path += (char)('0' + digit);
      }
      LocalCertificate cert, audited;
      double m = 0;
      std::string why = "no cage";
      bool ok = false;
      BigRat zero(0);
      if (FindBestCageForTriangle(tri, &seed, &cert, &m) &&
          ReauditCertificate(tri, cert, zero, zero, &audited, &why)) {
        ok = true;
      } else if (SynthesizeCertificate(tri, depth, zero, zero, &cert, false) &&
                 ReauditCertificate(tri, cert, zero, zero, &audited, &why)) {
        ok = true;
      }
      std::string diag;
      if (!ok) {
        vec3 c0 = ToDouble(tri.corners[0]), c1 = ToDouble(tri.corners[1]), c2 = ToDouble(tri.corners[2]);
        vec3 center = yocto::normalize((c0 + c1 + c2) / 3.0);
        std::vector<CandidateTriple> cands;
        GenerateCandidatesForView(center, tri, 8, true, 1e-13, &cands);
        std::map<std::string, int> reasons;
        int pass = 0;
        for (const auto &cd : cands) {
          ContactInfo cts[3] = {cd.contacts[0], cd.contacts[1], cd.contacts[2]};
          AxisCertificate ax; BigVecQ3 cent; BigRat del; std::string why2;
          if (AuditAxis(tri, cts, &ax, &cent, &del, &why2)) pass++;
          else reasons[why2.substr(0, why2.find('('))]++;
        }
        diag = StringPrintf(" [cands %zu, audit-pass %d;", cands.size(), pass);
        for (auto &[k, v] : reasons) diag += StringPrintf(" %s:%d", k.c_str(), v);
        diag += "]";
      }
      std::lock_guard<std::mutex> l(mu);
      printf("depth %2d path %-20s %s c=%.3e r=%s %s\n", depth, path.c_str(),
             ok ? "OK  " : "FAIL", ok ? audited.c.ToDouble() : 0.0,
             ok ? audited.r.ToString().c_str() : "-", ok ? "" : (why.substr(0, 60) + diag).c_str());
      fflush(stdout);
    }
  };
  for (int i = 0; i < 16; i++) threads.emplace_back(work);
  for (auto &th : threads) th.join();
  return 0;
}
