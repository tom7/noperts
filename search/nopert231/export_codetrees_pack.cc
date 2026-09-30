// export_codetrees_pack.cc: Program to export tubetree229 code trees (trees/tree.<id>.json)
// to Lean 4 packed format (.pack).

#include <iostream>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>
#include <queue>
#include <filesystem>

#include "tubetree229.h"
#include "tube229.h"
#include "base/logging.h"
#include "base/stringprintf.h"
#include "bignum/big-overloads.h"
#include "timer.h"

using namespace tubetree229;

static inline std::string ZigzagRatString(const BigRat &r) {
  BigInt num = r.Numerator();
  BigInt den = r.Denominator();
  BigInt zz = (num >= 0) ? (num * 2) : ((-num) * 2 - 1);
  return zz.ToString() + "," + den.ToString();
}

static void WriteAxisPack(std::ostream &out, const AxisCertificate &axis) {
  // edgeStart (3)
  for (int m = 0; m < 3; m++) out << "," << axis.contacts[m].edge_start;
  // edgeFinish (3)
  for (int m = 0; m < 3; m++) out << "," << axis.contacts[m].edge_finish;
  // edgeStart2 (3)
  for (int m = 0; m < 3; m++) out << "," << axis.contacts[m].edge_start2;
  // edgeFinish2 (3)
  for (int m = 0; m < 3; m++) out << "," << axis.contacts[m].edge_finish2;
  // mix (3)
  for (int m = 0; m < 3; m++) out << "," << axis.contacts[m].mix;
  // index (3)
  for (int m = 0; m < 3; m++) out << "," << axis.contacts[m].vertex;
  // nonzeroWitness (3)
  for (int m = 0; m < 3; m++) out << "," << std::max(0, axis.nonzero_witness[m]);
  // B
  out << "," << ZigzagRatString(axis.B);
}

struct LeanRow {
  int id = 0;
  bool is_leaf = false;
  std::string rel_path;
  int child_ids[4] = {-1, -1, -1, -1};
  const TreeNode *node = nullptr;
};

static bool ExportCodeTriangle(int code_id, int tri_idx, const TriangleQ &base_tri,
                               const TreeNode &root_node, const std::string &out_path,
                               int *out_num_rows, BigRat *out_r) {
  EffectiveBounds eff = ComputeEffectiveBounds(root_node);
  if (eff.r_lower <= BigRat(0)) {
    std::cerr << "Error: Code " << code_id << " Tri " << tri_idx << " r_lower <= 0!\n";
    return false;
  }
  *out_r = eff.r_lower;

  // BFS traversal to assign topological row IDs (0 <= parent_id < child_id < N)
  std::vector<LeanRow> rows;
  std::queue<int> q;

  rows.push_back({
    .id = 0,
    .is_leaf = false,
    .rel_path = "",
    .child_ids = {-1, -1, -1, -1},
    .node = &root_node
  });
  q.push(0);
  int next_id = 1;

  while (!q.empty()) {
    int curr_idx = q.front();
    q.pop();

    const TreeNode *n = rows[curr_idx].node;
    if (n->children.size() == 4) {
      rows[curr_idx].is_leaf = false;
      for (int c = 0; c < 4; c++) {
        CHECK(n->children[c] != nullptr);
        int cid = next_id++;
        rows[curr_idx].child_ids[c] = cid;
        std::string child_rel = rows[curr_idx].rel_path + std::to_string(c);
        rows.push_back({
          .id = cid,
          .is_leaf = false,
          .rel_path = child_rel,
          .child_ids = {-1, -1, -1, -1},
          .node = n->children[c].get()
        });
        q.push(cid);
      }
    } else {
      rows[curr_idx].is_leaf = true;
      if (!n->direct_cert.has_value() && !n->decomposed_cert.has_value()) {
        std::cerr << "Error: Leaf at path \"" << n->path << "\" lacks any certificate!\n";
        return false;
      }
    }
  }

  *out_num_rows = rows.size();

  std::ofstream out(out_path, std::ios::binary);
  if (!out.is_open()) {
    std::cerr << "Error: Failed to open output file " << out_path << "\n";
    return false;
  }

  // Header: count, symmetryIndex(0), ZigzagRatString(table_r),
  // followed by 9 rationals for base triangle corners [c0.x, c0.y, c0.z, c1.x, c1.y, c1.z, c2.x, c2.y, c2.z]
  out << rows.size() << ",0," << ZigzagRatString(eff.r_lower);
  for (int c = 0; c < 3; c++) {
    out << "," << ZigzagRatString(base_tri.corners[c].x)
        << "," << ZigzagRatString(base_tri.corners[c].y)
        << "," << ZigzagRatString(base_tri.corners[c].z);
  }

  for (size_t i = 0; i < rows.size(); i++) {
    const auto &r = rows[i];
    CHECK(r.id == (int)i);

    if (!r.is_leaf) {
      // Split row (tag 0):
      // tag, id, root(0), path_len, [path_digits], c0, c1, c2, c3
      out << ",0," << r.id << ",0," << r.rel_path.size();
      for (char ch : r.rel_path) {
        out << "," << (ch - '0');
      }
      out << "," << r.child_ids[0]
          << "," << r.child_ids[1]
          << "," << r.child_ids[2]
          << "," << r.child_ids[3];
    } else if (r.node->direct_cert.has_value()) {
      // Certificate row (tag 1):
      // tag, id, root(0), path_len, [path_digits], symmetryIndex(0),
      // [4 axes], c, delta, r
      TubeCertificate cert = r.node->direct_cert.value();
      out << ",1," << r.id << ",0," << r.rel_path.size();
      for (char ch : r.rel_path) {
        out << "," << (ch - '0');
      }
      out << "," << cert.symmetry_index;

      for (int a = 0; a < 4; a++) {
        WriteAxisPack(out, cert.axes[a]);
      }

      // c, delta, r
      out << "," << ZigzagRatString(cert.c)
          << "," << ZigzagRatString(cert.delta)
          << "," << ZigzagRatString(cert.r);
    } else if (r.node->decomposed_cert.has_value()) {
      auto dec = r.node->decomposed_cert.value();

      AxisCertificate coreAxis = dec.inner_core_axis;
      if (!dec.core_flock_axes.empty()) {
        coreAxis = dec.core_flock_axes[0];
      }

      // Decomposed Certificate row (tag 2):
      // Format: tag(2), id, root(0), path_len, [path_digits], symmetryIndex,
      // [4 axes: annular_axis, complement_axes[0..2]], c, delta, r,
      // coreAxis, defect0[0..2], D0, r_min, c_cone, c_core, lam, w[0..2]
      out << ",2," << r.id << ",0," << r.rel_path.size();
      for (char ch : r.rel_path) {
        out << "," << (ch - '0');
      }
      out << "," << dec.symmetry_index;

      // 4 certificate axes: annular_axis + 3 complement axes
      WriteAxisPack(out, dec.annular_axis);
      for (int a = 0; a < 3; a++) {
        WriteAxisPack(out, dec.complement_axes[a]);
      }

      // c (c_comp: complement cage margin), delta, r
      out << "," << ZigzagRatString(dec.c_comp)
          << "," << ZigzagRatString(dec.delta)
          << "," << ZigzagRatString(dec.r);

      // coreAxis
      WriteAxisPack(out, coreAxis);

      // defect0[0..2], D0, r_min, c_cone, c_core, lam, w[0..2]
      out << "," << ZigzagRatString(dec.defect0[0])
          << "," << ZigzagRatString(dec.defect0[1])
          << "," << ZigzagRatString(dec.defect0[2])
          << "," << ZigzagRatString(dec.defect_D)
          << "," << ZigzagRatString(dec.r_min)
          << "," << ZigzagRatString(dec.c_cone)
          << "," << ZigzagRatString(dec.c_core)
          << "," << ZigzagRatString(dec.lam)
          << "," << ZigzagRatString(dec.w[0])
          << "," << ZigzagRatString(dec.w[1])
          << "," << ZigzagRatString(dec.w[2]);
    } else {
      LOG(FATAL) << "Encountered leaf node without certificate: " << r.node->path;
    }
  }

  out << "\n";
  return true;
}

int main(int argc, char **argv) {
  std::string out_dir = ".artifacts/nopert229/packs";
  int single_code = -1;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--out_dir" && i + 1 < argc) {
      out_dir = argv[++i];
    } else if (arg == "--code" && i + 1 < argc) {
      single_code = std::stoi(argv[++i]);
    }
  }

  std::filesystem::create_directories(out_dir);
  std::string manifest_path = out_dir + "/manifest.txt";
  std::ofstream manifest(manifest_path);
  if (!manifest.is_open()) {
    std::cerr << "Failed to open manifest " << manifest_path << "\n";
    return 1;
  }

  int total_exported_triangles = 0;
  int total_exported_rows = 0;

  for (int code_idx = 0; code_idx < 79; code_idx++) {
    if (single_code >= 0 && code_idx != single_code) continue;

    std::string json_path = StringPrintf("trees/tree.%d.json", code_idx);
    if (!std::filesystem::exists(json_path)) {
      std::cout << "[Skip] " << json_path << " does not exist.\n";
      continue;
    }

    auto code_tree = LoadCodeTreeJson(json_path);
    if (!code_tree) {
      std::cerr << "[Error] Failed to load " << json_path << "\n";
      continue;
    }

    std::cout << "[Code " << code_idx << "] Exporting " << code_tree->triangles.size() << " triangles...\n";
    bool code_ok = true;
    for (size_t t = 0; t < code_tree->triangles.size(); t++) {
      const auto &ct = code_tree->triangles[t];
      std::string pack_name = StringPrintf("code_%d_tri_%zu.pack", code_idx, t);
      std::string pack_path = out_dir + "/" + pack_name;

      int num_rows = 0;
      BigRat r_lower;
      if (!ExportCodeTriangle(code_idx, t, ct.triangle, *ct.root, pack_path, &num_rows, &r_lower)) {
        std::cerr << "  [Warning] Code " << code_idx << " Tri " << t << " is incomplete, skipping.\n";
        code_ok = false;
        continue;
      }

      manifest << pack_name << " " << code_idx << " " << t << " " << num_rows << " " << r_lower.ToString() << "\n";
      total_exported_triangles++;
      total_exported_rows += num_rows;
    }
    if (code_ok) {
      std::cout << "  [Code " << code_idx << "] All triangles exported successfully.\n";
    }
  }

  manifest.close();
  std::cout << "\nExport Complete!\n"
            << "Total Triangles Exported: " << total_exported_triangles << "\n"
            << "Total Rows: " << total_exported_rows << "\n"
            << "Manifest: " << manifest_path << "\n";
  return 0;
}
