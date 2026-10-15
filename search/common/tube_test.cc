// Unit tests for the identity tube library (tube.h).
//
// Usage: tube_test.exe [TREES_DIR]
//
// The geometric tests are self-contained. The silhouette test uses the code
// triangles in ./codebdd.json (or $CODEBDD_JSON; skipped when it is absent).
// The audit test re-checks leaves of the tube
// trees in TREES_DIR (or $TREES_DIR), e.g. tuberefine's output; it is
// skipped when no trees directory is given.

#include "tube.h"

#include <array>
#include <cmath>
#include <cstdlib>
#include <filesystem>
#include <memory>
#include <iostream>
#include <set>
#include <string>
#include <vector>

#include "ansi.h"
#include "base/logging.h"
#include "base/print.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "model.h"
#include "rapidjson/document.h"
#include "test-data.h"
#include "tubetree.h"
#include "util.h"
#include "yocto-math.h"

using namespace tubetree;
using vec3 = yocto::vec<double, 3>;

static inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

// The first `max_tris` code triangles of codebdd.json, in order.
static std::vector<TriangleQ> LoadCodeTriangles(const std::string &bdd_json, int max_tris) {
  std::vector<TriangleQ> out;
  const std::string content = Util::ReadFile(bdd_json);
  if (content.empty()) return out;
  rapidjson::Document doc;
  doc.Parse(content.c_str());
  CHECK(!doc.HasParseError() && doc.HasMember("codes")) << bdd_json;
  for (const auto &code : doc["codes"].GetArray()) {
    for (const auto &tri : code["triangles"].GetArray()) {
      if ((int)out.size() >= max_tris) return out;
      TriangleQ tq;
      for (int k = 0; k < 3; k++) {
        tq.corners[k] = BigVecQ3(BigRat(tri[k]["x"].GetString()), BigRat(tri[k]["y"].GetString()),
                                 BigRat(tri[k]["z"].GetString()));
      }
      out.push_back(tq);
    }
  }
  return out;
}

// Silhouette contacts and candidate triples at the centroid of a code
// triangle: every contact must reference valid vertices.
static void TestBasicSilhouette(const TriangleQ &tri) {
  std::cout << "[RUN] TestBasicSilhouette\n";
  const vec3 centroid =
      (ToDouble(tri.corners[0]) + ToDouble(tri.corners[1]) + ToDouble(tri.corners[2])) / 3.0;

  std::vector<int> mixes = {0, 500, 1000};
  std::vector<ContactInfo> contacts = Tube::GenerateSilhouetteContacts(centroid, mixes);
  CHECK(!contacts.empty());
  for (const ContactInfo &c : contacts) {
    for (int v : {c.edge_start, c.edge_finish, c.edge_start2, c.edge_finish2, c.vertex}) {
      CHECK(v >= 0 && v < NUM_VERTICES) << v;
    }
    CHECK(c.mix >= 0 && c.mix <= kMixScale);
  }
  std::cout << "  Code triangle centroid produced " << contacts.size() << " silhouette contacts.\n";

  std::vector<Tube::CandidateTriple> triples = Tube::GenerateCandidateTriples(tri, contacts, 1e-12);
  std::cout << "  Code triangle produced " << triples.size() << " candidate triples.\n";
  std::cout << "[PASS] TestBasicSilhouette\n";
}

// Re-audits the leaf certificates of the tube trees written by tubecode /
// tuberefine (trees_dir/tree.<code>.json) with Tube's exact audit: every
// leaf must pass, with the same variation bound delta, and its stored
// (c, r) must satisfy the tube radius condition r^2 (1 + c^2) <= 4 c^2 with
// c no larger than the audited margin.
static void TestAuditTreeLeaves(const std::string &trees_dir, int num_codes, int max_leaves) {
  std::cout << "[RUN] TestAuditTreeLeaves\n";
  int audited_leaves = 0;
  for (int code = 0; code < num_codes; code++) {
    const std::string path = trees_dir + "/tree." + std::to_string(code) + ".json";
    std::unique_ptr<CodeTree> tree = LoadCodeTreeJson(path);
    CHECK(tree != nullptr) << "cannot load " << path;
    CHECK(tree->IsFullyCertified()) << path;
    int leaves = 0;
    for (const CodeTriangleTree &ct : tree->triangles) {
      auto visit = [&](auto &self, const TreeNode &node, const TriangleQ &tri) -> void {
        if (leaves >= max_leaves) return;
        if (!node.is_leaf()) {
          CHECK(node.children.size() == 4);
          TriangleQ ch[4];
          tri.Subdivide(ch);
          for (int c = 0; c < 4; c++) self(self, *node.children[c], ch[c]);
          return;
        }
        if (!node.direct_cert.has_value()) return;
        const TubeCertificate &stored = *node.direct_cert;
        TubeCertificate audited;
        std::string fail;
        CHECK(Tube::AuditCertificateAdaptive(tri, stored, &audited, &fail))
            << path << " leaf \"" << node.path << "\": " << fail;
        CHECK(audited.delta == stored.delta) << path << " leaf \"" << node.path << "\"";
        CHECK(stored.c > BigRat(0) && stored.c <= audited.c)
            << stored.c.ToString() << " vs " << audited.c.ToString();
        CHECK(stored.r > BigRat(0) &&
              stored.r * stored.r * (BigRat(1) + stored.c * stored.c) <=
                  BigRat(4) * stored.c * stored.c);
        leaves++;
      };
      CHECK(ct.root != nullptr);
      visit(visit, *ct.root, ct.triangle);
    }
    audited_leaves += leaves;
  }
  // (Trees after idcap's pass may have no direct-certificate leaves left.)
  if (audited_leaves == 0) std::cout << "  no direct-certificate leaves (e.g. trees after idcap's pass).\n";
  std::cout << "  " << audited_leaves << " leaves of " << num_codes << " codes re-audited.\n";
  std::cout << "[PASS] TestAuditTreeLeaves\n";
}

static void TestExtremalTetrahedron() {
  std::cout << "[RUN] TestExtremalTetrahedron\n";
  // 1. Point set enclosing the origin (vertices of an octahedron + noise)
  std::vector<vec3> pts = {
    { 1.0,  0.0,  0.0},
    {-1.0,  0.0,  0.0},
    { 0.0,  1.0,  0.0},
    { 0.0, -1.0,  0.0},
    { 0.0,  0.0,  1.0},
    { 0.0,  0.0, -1.0},
    { 0.5,  0.5,  0.5},
    {-0.5, -0.5, -0.5}
  };
  std::array<int, 4> indices;
  bool ok = Tube::FindExtremalTetrahedron(pts, &indices);
  CHECK(ok);
  double margin = 0;
  bool enclosed = Tube::PointInTetrahedron(
      vec3{0, 0, 0}, pts[indices[0]], pts[indices[1]], pts[indices[2]], pts[indices[3]], &margin);
  CHECK(enclosed && margin > 1e-6);
  std::cout << "  FindExtremalTetrahedron found enclosing tet: ["
            << indices[0] << ", " << indices[1] << ", " << indices[2] << ", " << indices[3]
            << "] margin=" << margin << "\n";

  // 2. Point set in upper half-space strictly excluding origin
  std::vector<vec3> upper_pts = {
    { 1.0,  0.0,  0.5},
    {-1.0,  0.0,  0.5},
    { 0.0,  1.0,  0.5},
    { 0.0, -1.0,  0.5},
    { 0.0,  0.0,  1.0}
  };
  std::array<int, 4> bad_indices;
  bool bad_ok = Tube::FindExtremalTetrahedron(upper_pts, &bad_indices);
  CHECK(!bad_ok);
  std::cout << "  Upper half-space points correctly rejected (cannot enclose origin).\n";
  std::cout << "[PASS] TestExtremalTetrahedron\n";
}

static void TestNearOriginFaceCuttingPlane() {
  std::cout << "[RUN] TestNearOriginFaceCuttingPlane\n";

  // Face perpendicular to z-axis, shifted by 8.854e-7 in +z direction:
  // Closest squared distance to origin is (8.854e-7)^2 = 7.84e-13 < 1e-12.
  const double d = 8.854e-7;
  vec3 p0 = {0.05, 0.0, d};
  vec3 p1 = {-0.025, 0.043301270189, d};
  vec3 p2 = {-0.025, -0.043301270189, d};
  // 4th point in initial pool on the SAME side (+z):
  vec3 p3 = {0.01, 0.01, 0.08};
  // Opposing candidate on the -z side:
  vec3 p4 = {-0.005, -0.005, -0.05};

  std::vector<vec3> pts = {p0, p1, p2, p3, p4};

  // Initial pool consists only of the +z points {0, 1, 2, 3}.
  std::set<int> pool = {0, 1, 2, 3};
  std::array<int, 4> simplex;
  double margin = 0;

  // With the premature early return bug (where closest.key < 1e-12 unconditionally
  // aborted without checking opposing candidates), this would fail on iteration 0.
  // With the fix, it orients the face normal away from the pool, searches in
  // direction -v, pulls in p4, and successfully cages the origin.
  bool ok = Tube::RefinePoolCuttingPlane(pts, &pool, &simplex, &margin);
  CHECK(ok);
  CHECK(margin > 1e-8);
  std::cout << "  RefinePoolCuttingPlane successfully caged origin! Margin = " << margin
            << ", simplex = [" << simplex[0] << ", " << simplex[1] << ", "
            << simplex[2] << ", " << simplex[3] << "]\n";

  // Also verify Wolfe's algorithm handles this near-origin face geometry
  std::vector<Tube::CandidateTriple> cands;
  for (size_t i = 0; i < pts.size(); i++) {
    Tube::CandidateTriple c;
    c.normalized_a = pts[i];
    cands.push_back(c);
  }
  std::array<int, 4> wolfe_simplex;
  bool wolfe_ok = Tube::FindBalancedTetrahedron(cands, &wolfe_simplex);
  CHECK(wolfe_ok);
  std::cout << "  FindBalancedTetrahedron successfully caged origin!\n";
  std::cout << "[PASS] TestNearOriginFaceCuttingPlane\n";
}

static void TestCheckAnnularDominance() {
  std::cout << "[RUN] TestCheckAnnularDominance\n";
  BigRat B = BigRat(176, 100);
  BigRat defect_D = BigRat(8, 10000000); // 8e-7
  BigRat c_cone = BigRat(99, 100);       // cos(cone) = 0.99
  BigRat delta = BigRat(333, 1000000000);// 3.33e-7

  // 1. Valid test with explicit radii: r_min = 1/10000, r = 1/2000
  BigRat r_min = BigRat(1, 10000);
  BigRat r = BigRat(1, 2000);
  bool ok = Tube::CheckAnnularDominance(B, defect_D, c_cone, delta, &r_min, &r);
  std::cout << "  CheckAnnularDominance (explicit radii): " << (ok ? "SUCCESS" : "FAIL") << "\n";
  CHECK(ok);

  // 2. Failure test with excessively large defect
  BigRat bad_defect = BigRat(1, 10);
  BigRat bad_r_min = r_min;
  BigRat bad_r = r;
  bool bad_ok = Tube::CheckAnnularDominance(B, bad_defect, c_cone, delta, &bad_r_min, &bad_r);
  std::cout << "  CheckAnnularDominance (excessive defect): correctly rejected (" << (!bad_ok ? "PASS" : "FAIL") << ")\n";
  CHECK(!bad_ok);

  // 3. Automatic solve mode (unspecified radii)
  BigRat auto_r_min{0};
  BigRat auto_r{0};
  bool auto_ok = Tube::CheckAnnularDominance(B, defect_D, c_cone, delta, &auto_r_min, &auto_r);
  std::cout << "  CheckAnnularDominance (auto solve): " << (auto_ok ? "SUCCESS" : "FAIL")
            << " r_min=" << auto_r_min.ToString() << " r=" << auto_r.ToString() << "\n";
  CHECK(auto_ok);
  CHECK(auto_r_min > BigRat(0));
  CHECK(auto_r > auto_r_min);

  std::cout << "[PASS] TestCheckAnnularDominance\n";
}

int main(int argc, char **argv) {
  ANSI::Init();
  const char *env_trees = getenv("TREES_DIR");
  const std::string trees_dir = argc > 1 ? argv[1] : (env_trees != nullptr ? env_trees : "");

  Print("=== Running Tube Unit Tests ===\n");
  TestExtremalTetrahedron();
  TestNearOriginFaceCuttingPlane();
  TestCheckAnnularDominance();

  if (HaveCodebddJson("TestBasicSilhouette")) {
    const std::vector<TriangleQ> tris = LoadCodeTriangles(CodebddJson(), 1);
    CHECK(!tris.empty()) << CodebddJson() << " has no code triangles";
    TestBasicSilhouette(tris[0]);
  }

  if (trees_dir.empty() || !std::filesystem::exists(trees_dir + "/tree.0.json")) {
    Print("SKIPPED: TestAuditTreeLeaves (no tube trees; pass TREES_DIR)\n");
  } else {
    TestAuditTreeLeaves(trees_dir, 2, 40);
  }
  Print("=== All Tube Unit Tests Passed! ===\n");
  Print("OK\n");
  return 0;
}
