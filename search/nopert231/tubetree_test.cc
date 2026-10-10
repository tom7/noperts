#include "tubetree.h"

#include <array>
#include <cassert>
#include <filesystem>
#include <format>
#include <string>
#include <utility>

#include <unistd.h>

#include "ansi.h"
#include "base/logging.h"
#include "base/print.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "util.h"

using namespace tubetree;

static void TestGeometry() {
  Print("Testing Geometry...\n");
  TriangleQ wedge = GetRootWedge();
  CHECK_EQ(wedge.corners[0].x, BigRat(1));
  CHECK_EQ(wedge.corners[0].y, BigRat(0));
  CHECK_EQ(wedge.corners[0].z, BigRat(0));

  CHECK_EQ(wedge.corners[1].x, BigRat(10, 41));
  CHECK_EQ(wedge.corners[1].y, BigRat(31, 41));
  CHECK_EQ(wedge.corners[1].z, BigRat(0));

  CHECK_EQ(wedge.corners[2].x, BigRat(0));
  CHECK_EQ(wedge.corners[2].y, BigRat(0));
  CHECK_EQ(wedge.corners[2].z, BigRat(1));

  TriangleQ children[4];
  wedge.Subdivide(children);

  TriangleQ path0 = TriangleFromPath("0");
  CHECK_EQ(path0.corners[0].x, children[0].corners[0].x);
  CHECK_EQ(path0.corners[1].x, children[0].corners[1].x);
  CHECK_EQ(path0.corners[2].x, children[0].corners[2].x);

  TriangleQ path3 = TriangleFromPath("3");
  CHECK_EQ(path3.corners[0].x, children[3].corners[0].x);
  CHECK_EQ(path3.corners[1].x, children[3].corners[1].x);
  CHECK_EQ(path3.corners[2].x, children[3].corners[2].x);

  TriangleQ path02 = TriangleFromPath("02");
  TriangleQ ch0_sub[4];
  children[0].Subdivide(ch0_sub);
  CHECK_EQ(path02.corners[0].x, ch0_sub[2].corners[0].x);
  CHECK_EQ(path02.corners[1].x, ch0_sub[2].corners[1].x);
  CHECK_EQ(path02.corners[2].x, ch0_sub[2].corners[2].x);
  Print("Geometry tests PASSED.\n");
}

static void TestBounds() {
  Print("Testing Bounds...\n");
  // 1. Single leaf node with direct certificate
  TreeNode leaf;
  leaf.path = "0";
  leaf.direct_bounds.direct_r_lower = BigRat(1, 50000);
  leaf.direct_bounds.direct_r_upper = BigRat(1, 20000);
  leaf.direct_bounds.direct_c_lower = BigRat(1, 100000);
  leaf.direct_bounds.direct_c_upper = BigRat(1, 40000);

  EffectiveBounds eb = ComputeEffectiveBounds(leaf);
  CHECK(eb.complete);
  CHECK_EQ(eb.r_lower, BigRat(1, 50000));
  CHECK_EQ(eb.r_upper, BigRat(1, 20000));

  // 2. Interior node with direct certificate and 4 superior children
  auto root = std::make_unique<TreeNode>();
  root->path = "0";
  root->direct_bounds.direct_r_lower = BigRat(1, 50000);
  root->direct_bounds.direct_r_upper = BigRat(1, 10000); // 0.000100

  for (int i = 0; i < 4; i++) {
    auto ch = std::make_unique<TreeNode>();
    ch->path = "0" + std::to_string(i);
    ch->direct_bounds.direct_r_lower = BigRat(1, 10000); // 5x better!
    ch->direct_bounds.direct_r_upper = BigRat(1, 15000);
    root->children.push_back(std::move(ch));
  }

  EffectiveBounds root_eb = ComputeEffectiveBounds(*root);
  CHECK(root_eb.complete);
  // Collective children bound is superior: 1/10000 > 1/50000
  CHECK_EQ(root_eb.r_lower, BigRat(1, 10000));
  CHECK_EQ(root_eb.r_upper, BigRat(1, 15000));

  // 3. Incomplete children: 3 children resolved, 1 child unresolved (r_lower = 0)
  root->children[3]->direct_bounds.direct_r_lower = BigRat(0);
  EffectiveBounds fallback_eb = ComputeEffectiveBounds(*root);
  // Crucial test: Does it fall back to the umbrella direct certificate?
  CHECK(fallback_eb.complete);
  CHECK_EQ(fallback_eb.r_lower, BigRat(1, 50000)); // Umbrella saved it!
  Print("Bounds tests PASSED.\n");
}

static void TestSerializationAndSubtree() {
  Print("Testing Serialization and Subtree detachment...\n");
  std::string tmp_dir = std::format("/tmp/tubetree_test.{}", (int)getpid());
  std::filesystem::create_directories(tmp_dir);

  auto root = std::make_unique<TreeNode>();
  root->path = "0";
  root->direct_bounds.direct_r_lower = BigRat(1, 50000);
  root->direct_bounds.direct_r_upper = BigRat(1, 20000);

  for (int i = 0; i < 4; i++) {
    auto ch = std::make_unique<TreeNode>();
    ch->path = "0" + std::to_string(i);
    ch->direct_bounds.direct_r_lower = BigRat(1, 10000);
    ch->direct_bounds.direct_r_upper = BigRat(1, 15000);
    root->children.push_back(std::move(ch));
  }

  // Add grandchild to child 1
  for (int j = 0; j < 4; j++) {
    auto gch = std::make_unique<TreeNode>();
    gch->path = "01" + std::to_string(j);
    gch->direct_bounds.direct_r_lower = BigRat(1, 5000);
    root->children[1]->children.push_back(std::move(gch));
  }

  TreeStats s_orig = ComputeTreeStats(*root);
  CHECK_EQ(s_orig.total_nodes, 9); // root(1) + children(4) + grandchildren(4)
  CHECK_EQ(s_orig.max_depth, 3);

  std::string main_file = tmp_dir + "/tree_main.json";
  CHECK(SaveTreeJson(*root, main_file, /*shallow=*/false));

  auto loaded = LoadTreeJson(main_file, /*load_external=*/false);
  CHECK(loaded != nullptr);
  TreeStats s_loaded = ComputeTreeStats(*loaded);
  CHECK_EQ(s_loaded.total_nodes, 9);
  CHECK_EQ(loaded->children[1]->children.size(), 4);

  // Now test subtree detachment: detach child 1 into its own file
  CHECK(DetachSubtreeToFile(loaded->children[1].get(), tmp_dir));
  CHECK(loaded->children[1]->external);
  CHECK(loaded->children[1]->children.empty());

  TreeStats s_detached = ComputeTreeStats(*loaded);
  CHECK_EQ(s_detached.total_nodes, 5); // grandchildren are now external
  CHECK_EQ(s_detached.external_refs, 1);

  // Re-save shallow tree
  CHECK(SaveTreeJson(*loaded, main_file, /*shallow=*/true));

  // Reload shallow tree without external
  auto loaded_shallow = LoadTreeJson(main_file, /*load_external=*/false, tmp_dir);
  CHECK(loaded_shallow != nullptr);
  CHECK(loaded_shallow->children[1]->external);
  CHECK(loaded_shallow->children[1]->children.empty());

  // Reload tree WITH external resolution
  auto loaded_deep = LoadTreeJson(main_file, /*load_external=*/true, tmp_dir);
  CHECK(loaded_deep != nullptr);
  CHECK(!loaded_deep->children[1]->external);
  CHECK_EQ(loaded_deep->children[1]->children.size(), 4);
  TreeStats s_deep = ComputeTreeStats(*loaded_deep);
  CHECK_EQ(s_deep.total_nodes, 9);

  std::filesystem::remove_all(tmp_dir);
  Print("Serialization and Subtree tests PASSED.\n");
}

static inline vec3 VtoD(const BigVecQ3 &v) {
  return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

// A synthetic tree: root `prefix` with direct radius `root_r` and four
// leaf children with radii `child_r[i]`.
static std::unique_ptr<TreeNode> SyntheticTree(const std::string &prefix, const BigRat &root_r,
                                               const std::array<BigRat, 4> &child_r) {
  auto root = std::make_unique<TreeNode>();
  root->path = prefix;
  root->direct_bounds.direct_r_lower = root_r;
  for (int i = 0; i < 4; i++) {
    auto ch = std::make_unique<TreeNode>();
    ch->path = prefix + std::to_string(i);
    ch->direct_bounds.direct_r_lower = child_r[i];
    root->children.push_back(std::move(ch));
  }
  return root;
}

static void TestTubeAtlas() {
  Print("Testing TubeAtlas...\n");
  TubeAtlas atlas;
  CHECK(!atlas.IsLoaded());

  std::string tmp_dir = std::format("/tmp/tubetree_test_atlas.{}", (int)getpid());
  std::filesystem::remove_all(tmp_dir);
  std::filesystem::create_directories(tmp_dir);
  CHECK_EQ(atlas.LoadFromDir(tmp_dir), 0);
  CHECK(!atlas.IsLoaded());

  // Tree 3: every child certified, so the root's effective radius is the
  // larger of its own and the smallest child's.
  const BigRat r_child(1, 10000);
  CHECK(SaveTreeJson(*SyntheticTree("3", BigRat(1, 50000), {r_child, r_child, BigRat(1, 5000), r_child}),
                     tmp_dir + "/tree_3.json", /*shallow=*/false));
  // Tree 0: child 2 uncertified, so the root is not certified, but its
  // certified children are.
  CHECK(SaveTreeJson(*SyntheticTree("0", BigRat(0), {r_child, r_child, BigRat(0), r_child}),
                     tmp_dir + "/tree_0.json", /*shallow=*/false));

  CHECK_EQ(atlas.LoadFromDir(tmp_dir), 2);
  CHECK(atlas.IsLoaded());
  CHECK(atlas.IsLoaded(3) && atlas.IsLoaded(0) && !atlas.IsLoaded(1));

  CHECK(atlas.GetSafeRadiusRatForPath("3") == r_child);
  CHECK(atlas.GetSafeRadiusRatForPath("32") == BigRat(1, 5000));
  // A path below a leaf stops at the leaf.
  CHECK(atlas.GetSafeRadiusRatForPath("3000") == r_child);
  {
    TriangleQ t3 = TriangleFromPath("3");
    vec3 corners[3] = {VtoD(t3.corners[0]), VtoD(t3.corners[1]), VtoD(t3.corners[2])};
    CHECK_EQ(atlas.GetSafeRadiusForTriangle(corners), atlas.GetSafeRadiusForPath("3"));
  }

  CHECK(atlas.GetSafeRadiusRatForPath("0") == BigRat(0));
  CHECK(atlas.GetSafeRadiusRatForPath("01") == r_child);
  CHECK(atlas.GetSafeRadiusRatForPath("1") == BigRat(0));

  std::filesystem::remove_all(tmp_dir);
  Print("TubeAtlas tests PASSED.\n");
}

static void TestNearestCertifiedNode() {
  Print("Testing Nearest Certified Node Queries...\n");

  // 1. Synthetic TreeNode test
  TreeNode root;
  root.path = "";
  for (int i = 0; i < 4; i++) {
    auto child = std::make_unique<TreeNode>();
    child->path = std::to_string(i);
    root.children.push_back(std::move(child));
  }
  // Only child 2 is certified
  root.children[2]->direct_bounds.direct_r_lower = BigRat(1, 5000);

  // Direction in child 2
  TriangleQ t2 = TriangleFromPath("2");
  vec3 c2 = (VtoD(t2.corners[0]) + VtoD(t2.corners[1]) + VtoD(t2.corners[2])) * (1.0 / 3.0);
  auto res2 = FindNearestCertifiedNode(root, c2);
  CHECK(res2.has_value());
  CHECK_EQ(res2->path, "2");
  CHECK(res2->contains_direction);
  CHECK_EQ(res2->angular_distance, 0.0);
  CHECK_EQ(res2->direct_r_lower, 0.0002);

  // Direction in child 0 (uncertified) -> should find child 2 as nearest
  TriangleQ t0 = TriangleFromPath("0");
  vec3 c0 = (VtoD(t0.corners[0]) + VtoD(t0.corners[1]) + VtoD(t0.corners[2])) * (1.0 / 3.0);
  auto res0 = FindNearestCertifiedNode(root, c0);
  CHECK(res0.has_value());
  CHECK_EQ(res0->path, "2");
  CHECK(!res0->contains_direction);
  CHECK(res0->angular_distance > 0.0);
  CHECK_EQ(res0->direct_r_lower, 0.0002);

  Print("Nearest Certified Node tests PASSED.\n");
}

static void TestDecomposedCertificate() {
  Print("Testing DecomposedCertificate in memory and serialization...\n");

  DecomposedCertificate dc;
  dc.r_min = BigRat(1, 10000);
  dc.r = BigRat(1, 2000);
  dc.c_cone = BigRat(1, 10);
  dc.delta = BigRat(333, 1000000000);
  dc.defect_D = BigRat(8, 10000000);
  dc.c_comp = BigRat(5691, 125000);
  dc.symmetry_index = 0;
  dc.inner_index[0] = 2;
  dc.inner_index[1] = 4;
  dc.inner_index[2] = 15;

  // Inner core axis
  dc.inner_core_axis.B = BigRat(242645731, 1000000000);
  dc.inner_core_axis.nonzero_witness[0] = 15;
  dc.inner_core_axis.nonzero_witness[1] = 1;
  dc.inner_core_axis.nonzero_witness[2] = 15;
  dc.inner_core_axis.contacts[0] = {1, 0, 0, 4, 1000, 1};
  dc.inner_core_axis.contacts[1] = {10, 15, 15, 19, 1000, 15};
  dc.inner_core_axis.contacts[2] = {2, 1, 1, 0, 1000, 1};

  // Annular axis
  dc.annular_axis.B = BigRat(176, 100);
  dc.annular_axis.nonzero_witness[0] = 1;
  dc.annular_axis.nonzero_witness[1] = 1;
  dc.annular_axis.nonzero_witness[2] = 1;
  dc.annular_axis.contacts[0] = {3, 2, 2, 1, 800, 2};
  dc.annular_axis.contacts[1] = {1, 4, 4, 8, 800, 4};
  dc.annular_axis.contacts[2] = {13, 14, 14, 15, 200, 14};

  // 3 Complement axes
  dc.complement_axes.resize(3);
  dc.complement_axes[0].B = BigRat(3, 2);
  dc.complement_axes[0].nonzero_witness[0] = 9;
  dc.complement_axes[0].nonzero_witness[1] = 19;
  dc.complement_axes[0].nonzero_witness[2] = 1;
  dc.complement_axes[0].contacts[0] = {15, 19, 19, 3, 200, 19};
  dc.complement_axes[0].contacts[1] = {2, 1, 1, 4, 200, 1};
  dc.complement_axes[0].contacts[2] = {8, 9, 9, 10, 200, 9};

  dc.complement_axes[1].B = BigRat(13, 10);
  dc.complement_axes[1].nonzero_witness[0] = 9;
  dc.complement_axes[1].nonzero_witness[1] = 19;
  dc.complement_axes[1].nonzero_witness[2] = 1;
  dc.complement_axes[1].contacts[0] = {2, 1, 1, 4, 0, 1};
  dc.complement_axes[1].contacts[1] = {10, 15, 15, 19, 333, 15};
  dc.complement_axes[1].contacts[2] = {10, 15, 15, 19, 0, 15};

  dc.complement_axes[2].B = BigRat(132412734, 100000000);
  dc.complement_axes[2].nonzero_witness[0] = 9;
  dc.complement_axes[2].nonzero_witness[1] = 19;
  dc.complement_axes[2].nonzero_witness[2] = 1;
  dc.complement_axes[2].contacts[0] = {3, 2, 2, 1, 800, 2};
  dc.complement_axes[2].contacts[1] = {4, 8, 8, 9, 800, 8};
  dc.complement_axes[2].contacts[2] = {14, 15, 15, 19, 800, 15};

  // 1. In-memory TreeNode properties
  TreeNode leaf;
  leaf.path = "031213002112122012121";
  leaf.decomposed_cert = dc;

  CHECK(leaf.has_certificate());
  CHECK_EQ(leaf.GetCertifiedRadius(), BigRat(1, 2000));

  EffectiveBounds eb = ComputeEffectiveBounds(leaf);
  CHECK(eb.complete);
  CHECK_EQ(eb.r_lower, BigRat(1, 2000));
  CHECK_EQ(eb.c_lower, BigRat(5691, 125000));

  TreeStats s = ComputeTreeStats(leaf);
  CHECK_EQ(s.total_nodes, 1);
  CHECK_EQ(s.leaves, 1);
  CHECK_EQ(s.direct_certificates, 0);
  CHECK_EQ(s.decomposed_certificates, 1);

  // 2. JSON Serialization and Round-trip Deserialization
  std::string tmp_dir = std::format("/tmp/tubetree_decomp_test.{}", (int)getpid());
  std::filesystem::create_directories(tmp_dir);
  std::string json_path = tmp_dir + "/leaf_decomp.json";

  CHECK(SaveTreeJson(leaf, json_path, /*shallow=*/false));

  auto loaded = LoadTreeJson(json_path, /*load_external=*/false);
  CHECK(loaded != nullptr);
  CHECK_EQ(loaded->path, leaf.path);
  CHECK(loaded->has_certificate());
  CHECK(loaded->decomposed_cert.has_value());

  const auto &ldc = loaded->decomposed_cert.value();
  CHECK_EQ(ldc.r_min, dc.r_min);
  CHECK_EQ(ldc.r, dc.r);
  CHECK_EQ(ldc.c_cone, dc.c_cone);
  CHECK_EQ(ldc.delta, dc.delta);
  CHECK_EQ(ldc.defect_D, dc.defect_D);
  CHECK_EQ(ldc.c_comp, dc.c_comp);
  CHECK_EQ(ldc.symmetry_index, dc.symmetry_index);
  CHECK_EQ(ldc.inner_index[0], 2);
  CHECK_EQ(ldc.inner_index[1], 4);
  CHECK_EQ(ldc.inner_index[2], 15);

  CHECK_EQ(ldc.inner_core_axis.B, dc.inner_core_axis.B);
  CHECK_EQ(ldc.inner_core_axis.nonzero_witness[0], 15);
  CHECK_EQ(ldc.inner_core_axis.contacts[1].vertex, 15);

  CHECK_EQ(ldc.annular_axis.B, dc.annular_axis.B);
  CHECK_EQ(ldc.annular_axis.contacts[0].vertex, 2);

  CHECK_EQ(ldc.complement_axes.size(), 3);
  CHECK_EQ(ldc.complement_axes[0].B, dc.complement_axes[0].B);
  CHECK_EQ(ldc.complement_axes[0].contacts[0].vertex, 19);
  CHECK_EQ(ldc.complement_axes[2].contacts[2].vertex, 15);

  EffectiveBounds loaded_eb = ComputeEffectiveBounds(*loaded);
  CHECK(loaded_eb.complete);
  CHECK_EQ(loaded_eb.r_lower, BigRat(1, 2000));
  CHECK_EQ(loaded_eb.c_lower, BigRat(5691, 125000));

  // 3. Mixed tree test: Root with 3 standard certificate leaves and 1 decomposed certificate leaf
  auto parent = std::make_unique<TreeNode>();
  parent->path = "0";

  for (int i = 0; i < 3; i++) {
    auto ch = std::make_unique<TreeNode>();
    ch->path = "0" + std::to_string(i);
    TubeCertificate std_cert;
    std_cert.r = BigRat(1, 1000);
    std_cert.c = BigRat(1, 500);
    std_cert.delta = BigRat(1, 100000);
    std_cert.axes[0].B = BigRat(1);
    ch->direct_cert = std_cert;
    parent->children.push_back(std::move(ch));
  }
  // Child 3 is our decomposed certificate leaf
  auto ch3 = std::make_unique<TreeNode>();
  ch3->path = "03";
  ch3->decomposed_cert = dc;
  parent->children.push_back(std::move(ch3));

  EffectiveBounds parent_eb = ComputeEffectiveBounds(*parent);
  CHECK(parent_eb.complete);
  // Min over children: min(1/1000, 1/1000, 1/1000, 1/2000) = 1/2000
  CHECK_EQ(parent_eb.r_lower, BigRat(1, 2000));

  TreeStats ps = ComputeTreeStats(*parent);
  CHECK_EQ(ps.total_nodes, 5);
  CHECK_EQ(ps.leaves, 4);
  CHECK_EQ(ps.direct_certificates, 3);
  CHECK_EQ(ps.decomposed_certificates, 1);

  std::string mixed_json = tmp_dir + "/mixed_tree.json";
  CHECK(SaveTreeJson(*parent, mixed_json, /*shallow=*/false));

  auto loaded_parent = LoadTreeJson(mixed_json, /*load_external=*/false);
  CHECK(loaded_parent != nullptr);
  TreeStats lps = ComputeTreeStats(*loaded_parent);
  CHECK_EQ(lps.total_nodes, 5);
  CHECK_EQ(lps.direct_certificates, 3);
  CHECK_EQ(lps.decomposed_certificates, 1);
  CHECK(loaded_parent->children[3]->decomposed_cert.has_value());
  CHECK(loaded_parent->children[0]->direct_cert.has_value());

  std::filesystem::remove_all(tmp_dir);
  Print("DecomposedCertificate tests PASSED.\n");
}

int main() {
  ANSI::Init();

  TestGeometry();
  TestBounds();
  TestSerializationAndSubtree();
  TestTubeAtlas();
  TestNearestCertifiedNode();
  TestDecomposedCertificate();

  Print("\nALL TUBETREE TESTS PASSED SUCCESSFULLY!\n");
  return 0;
}

