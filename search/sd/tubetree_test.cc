#include "tubetree.h"

#include <filesystem>
#include <memory>
#include <string>
#include <utility>

#include "ansi.h"
#include "base/logging.h"
#include "base/print.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "util.h"

using namespace tubetree;

static TriangleQ SomeTriangle() {
  TriangleQ t;
  t.corners[0] = BigVecQ3(BigRat(0), BigRat(0), BigRat(1));
  t.corners[1] = BigVecQ3(BigRat(500, 1343), BigRat(160, 1343), BigRat(683, 1343));
  t.corners[2] = BigVecQ3(BigRat(250, 1281), BigRat(115, 427), BigRat(98, 183));
  return t;
}

static bool SameTriangle(const TriangleQ &a, const TriangleQ &b) {
  for (int k = 0; k < 3; k++) {
    if (!(a.corners[k].x == b.corners[k].x && a.corners[k].y == b.corners[k].y &&
          a.corners[k].z == b.corners[k].z)) {
      return false;
    }
  }
  return true;
}

static void TestGeometry() {
  Print("Testing Geometry...\n");
  const TriangleQ t = SomeTriangle();
  TriangleQ ch[4];
  t.Subdivide(ch);

  const BigVecQ3 m01 = (t.corners[0] + t.corners[1]) / BigRat(2);
  const BigVecQ3 m12 = (t.corners[1] + t.corners[2]) / BigRat(2);
  const BigVecQ3 m20 = (t.corners[2] + t.corners[0]) / BigRat(2);
  CHECK(SameTriangle(ch[0], TriangleQ{t.corners[0], m01, m20}));
  CHECK(SameTriangle(ch[1], TriangleQ{m01, t.corners[1], m12}));
  CHECK(SameTriangle(ch[2], TriangleQ{m20, m12, t.corners[2]}));
  CHECK(SameTriangle(ch[3], TriangleQ{m01, m12, m20}));

  // GetTriangle returns the explicit triangle.
  TreeNode node;
  node.explicit_triangle = ch[2];
  CHECK(SameTriangle(node.GetTriangle(), ch[2]));
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

  // 2. Interior node with direct certificate and 4 better children
  auto root = std::make_unique<TreeNode>();
  root->path = "0";
  root->direct_bounds.direct_r_lower = BigRat(1, 50000);
  root->direct_bounds.direct_r_upper = BigRat(1, 10000);

  for (int i = 0; i < 4; i++) {
    auto ch = std::make_unique<TreeNode>();
    ch->path = "0" + std::to_string(i);
    ch->direct_bounds.direct_r_lower = BigRat(1, 10000);
    ch->direct_bounds.direct_r_upper = BigRat(1, 15000);
    root->children.push_back(std::move(ch));
  }

  EffectiveBounds root_eb = ComputeEffectiveBounds(*root);
  CHECK(root_eb.complete);
  // The children's collective bound is better: 1/10000 > 1/50000.
  CHECK_EQ(root_eb.r_lower, BigRat(1, 10000));
  CHECK_EQ(root_eb.r_upper, BigRat(1, 15000));

  // 3. Incomplete children: one child unresolved (r_lower = 0) falls back
  // to the parent's own certificate.
  root->children[3]->direct_bounds.direct_r_lower = BigRat(0);
  EffectiveBounds fallback_eb = ComputeEffectiveBounds(*root);
  CHECK(fallback_eb.complete);
  CHECK_EQ(fallback_eb.r_lower, BigRat(1, 50000));
  Print("Bounds tests PASSED.\n");
}

// A synthetic axis certificate (values only matter for the round trip).
static AxisCertificate SomeAxis(int seed) {
  AxisCertificate ax;
  ax.B = BigRat(100 + seed, 7);
  for (int m = 0; m < 3; m++) {
    ax.nonzero_witness[m] = seed + m;
    ax.contacts[m] = {seed + m, seed + m + 1, seed + m + 1, seed + m + 2,
                      (seed * 137 + m * 311) % (kMixScale + 1), seed + m + 1};
  }
  return ax;
}

static bool SameAxis(const AxisCertificate &a, const AxisCertificate &b) {
  if (!(a.B == b.B)) return false;
  for (int m = 0; m < 3; m++) {
    if (a.nonzero_witness[m] != b.nonzero_witness[m]) return false;
    const ContactInfo &x = a.contacts[m], &y = b.contacts[m];
    if (x.edge_start != y.edge_start || x.edge_finish != y.edge_finish ||
        x.edge_start2 != y.edge_start2 || x.edge_finish2 != y.edge_finish2 ||
        x.mix != y.mix || x.vertex != y.vertex) {
      return false;
    }
  }
  return true;
}

static DecomposedCertificate SomeDecomposedCertificate() {
  DecomposedCertificate dc;
  dc.r_min = BigRat(1, 10000);
  dc.r = BigRat(1, 2000);
  dc.c_cone = BigRat(1, 10);
  dc.delta = BigRat(333, 1000000000);
  dc.defect_D = BigRat(8, 10000000);
  dc.c_comp = BigRat(5691, 125000);
  dc.c_core = BigRat(2, 1000);
  dc.lam = BigRat(3, 5);
  dc.defect0 = {BigRat(1, 3), BigRat(1, 5), BigRat(1, 7)};
  dc.w = {BigRat(1, 2), BigRat(1, 4), BigRat(1, 4)};
  dc.symmetry_index = 0;
  dc.inner_index[0] = 2;
  dc.inner_index[1] = 4;
  dc.inner_index[2] = 9;
  dc.inner_core_axis = SomeAxis(1);
  dc.annular_axis = SomeAxis(5);
  for (int i = 0; i < 3; i++) dc.complement_axes.push_back(SomeAxis(10 + i));
  for (int i = 0; i < 2; i++) dc.core_flock_axes.push_back(SomeAxis(20 + i));
  return dc;
}

static void TestDecomposedCertificate() {
  Print("Testing DecomposedCertificate in memory...\n");
  TreeNode leaf;
  leaf.path = "0123";
  leaf.decomposed_cert = SomeDecomposedCertificate();

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
  Print("DecomposedCertificate tests PASSED.\n");
}

// Round trip of the per-code tree format (tubetree_code_v1): one triangle
// split once, with three 4-axis leaves and one decomposed leaf, and a
// second triangle that is a single leaf.
static void TestCodeTreeRoundTrip() {
  Print("Testing CodeTree serialization...\n");
  CodeTree tree;
  tree.code_id = 7;
  tree.code_hex = "0123abcd";

  const TriangleQ t = SomeTriangle();
  TriangleQ ch[4];
  t.Subdivide(ch);

  TubeCertificate cert;
  cert.r = BigRat(1, 1000);
  cert.c = BigRat(1, 500);
  cert.delta = BigRat(1, 100000);
  for (int a = 0; a < 4; a++) cert.axes[a] = SomeAxis(30 + a);

  {
    CodeTriangleTree ct;
    ct.triangle_index = 0;
    ct.triangle = t;
    ct.root = std::make_unique<TreeNode>();
    ct.root->path = "";
    for (int i = 0; i < 4; i++) {
      auto node = std::make_unique<TreeNode>();
      node->path = std::to_string(i);
      node->explicit_triangle = ch[i];
      if (i < 3) {
        node->direct_cert = cert;
        node->direct_bounds.direct_r_lower = cert.r;
        node->direct_bounds.direct_c_lower = cert.c;
      } else {
        node->decomposed_cert = SomeDecomposedCertificate();
      }
      ct.root->children.push_back(std::move(node));
    }
    tree.triangles.push_back(std::move(ct));
  }
  {
    CodeTriangleTree ct;
    ct.triangle_index = 1;
    ct.triangle = ch[3];
    ct.root = std::make_unique<TreeNode>();
    ct.root->direct_cert = cert;
    tree.triangles.push_back(std::move(ct));
  }
  CHECK(tree.IsFullyCertified());
  CHECK_EQ(tree.TotalLeaves(), 5);

  const std::string tmp_dir =
      (std::filesystem::temp_directory_path() / "tubetree_test").string();
  std::filesystem::create_directories(tmp_dir);
  const std::string json_path = tmp_dir + "/tree.7.json";
  CHECK(SaveCodeTreeJson(tree, json_path));

  std::unique_ptr<CodeTree> loaded = LoadCodeTreeJson(json_path);
  CHECK(loaded != nullptr);
  CHECK_EQ(loaded->code_id, 7);
  CHECK_EQ(loaded->code_hex, "0123abcd");
  CHECK_EQ(loaded->triangles.size(), 2);
  CHECK(loaded->IsFullyCertified());
  CHECK_EQ(loaded->TotalLeaves(), 5);
  CHECK_EQ(loaded->triangles[1].triangle_index, 1);
  CHECK(SameTriangle(loaded->triangles[0].triangle, t));
  CHECK(SameTriangle(loaded->triangles[1].triangle, ch[3]));

  const TreeNode &root = *loaded->triangles[0].root;
  TreeStats ps = ComputeTreeStats(root);
  CHECK_EQ(ps.total_nodes, 5);
  CHECK_EQ(ps.leaves, 4);
  CHECK_EQ(ps.split_nodes, 1);
  CHECK_EQ(ps.direct_certificates, 3);
  CHECK_EQ(ps.decomposed_certificates, 1);
  CHECK_EQ(ps.max_depth, 1);
  // Min over children: min(1/1000, 1/1000, 1/1000, 1/2000) = 1/2000
  CHECK_EQ(ComputeEffectiveBounds(root).r_lower, BigRat(1, 2000));

  for (int i = 0; i < 3; i++) {
    const TreeNode &n = *root.children[i];
    CHECK_EQ(n.path, std::to_string(i));
    CHECK(n.direct_cert.has_value());
    CHECK_EQ(n.direct_cert->r, cert.r);
    CHECK_EQ(n.direct_cert->c, cert.c);
    CHECK_EQ(n.direct_cert->delta, cert.delta);
    for (int a = 0; a < 4; a++) CHECK(SameAxis(n.direct_cert->axes[a], cert.axes[a]));
  }

  const DecomposedCertificate dc = SomeDecomposedCertificate();
  CHECK(root.children[3]->decomposed_cert.has_value());
  const DecomposedCertificate &ldc = *root.children[3]->decomposed_cert;
  CHECK_EQ(ldc.r_min, dc.r_min);
  CHECK_EQ(ldc.r, dc.r);
  CHECK_EQ(ldc.c_cone, dc.c_cone);
  CHECK_EQ(ldc.delta, dc.delta);
  CHECK_EQ(ldc.defect_D, dc.defect_D);
  CHECK_EQ(ldc.c_comp, dc.c_comp);
  CHECK_EQ(ldc.c_core, dc.c_core);
  CHECK_EQ(ldc.lam, dc.lam);
  for (int i = 0; i < 3; i++) {
    CHECK_EQ(ldc.defect0[i], dc.defect0[i]);
    CHECK_EQ(ldc.w[i], dc.w[i]);
    CHECK_EQ(ldc.inner_index[i], dc.inner_index[i]);
  }
  CHECK(SameAxis(ldc.inner_core_axis, dc.inner_core_axis));
  CHECK(SameAxis(ldc.annular_axis, dc.annular_axis));
  CHECK_EQ(ldc.complement_axes.size(), dc.complement_axes.size());
  for (size_t i = 0; i < dc.complement_axes.size(); i++)
    CHECK(SameAxis(ldc.complement_axes[i], dc.complement_axes[i]));
  CHECK_EQ(ldc.core_flock_axes.size(), dc.core_flock_axes.size());
  for (size_t i = 0; i < dc.core_flock_axes.size(); i++)
    CHECK(SameAxis(ldc.core_flock_axes[i], dc.core_flock_axes[i]));

  std::filesystem::remove_all(tmp_dir);
  Print("CodeTree serialization tests PASSED.\n");
}

int main() {
  ANSI::Init();

  TestGeometry();
  TestBounds();
  TestDecomposedCertificate();
  TestCodeTreeRoundTrip();

  Print("\nALL TUBETREE TESTS PASSED SUCCESSFULLY!\n");
  return 0;
}
