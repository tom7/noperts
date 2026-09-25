// export_tubetree_pack.cc: Standalone program to export a tubetree229 JSON tree
// to the Lean 4 packed format (.pack) decoded by PackedLocalViewTree.lean.
//
// Usage:
//   ./export_tubetree_pack.exe --input .artifacts/nopert229/tree_2.json --output .artifacts/nopert229/local-view2.pack

#include <iostream>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>
#include <queue>
#include <filesystem>

#include "tubetree229.h"
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

int main(int argc, char **argv) {
  std::string input_path;
  std::string output_path;
  bool prune_at_cert = false;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--input" && i + 1 < argc) {
      input_path = argv[++i];
    } else if (arg == "--output" && i + 1 < argc) {
      output_path = argv[++i];
    } else if (arg == "--prune_at_cert") {
      prune_at_cert = true;
    } else if (arg == "--help" || arg == "-h") {
      std::cout << "Usage: " << argv[0] << " --input <tree.json> --output <local-view.pack> [--prune_at_cert]\n";
      return 0;
    } else {
      std::cerr << "Unknown argument: " << arg << "\n";
      return 1;
    }
  }

  if (input_path.empty() || output_path.empty()) {
    std::cerr << "Error: --input and --output are required.\n";
    return 1;
  }

  std::cout << "Loading tree from " << input_path << "...\n";
  Timer load_timer;
  std::string base_dir = std::filesystem::path(input_path).parent_path().string();
  std::unique_ptr<TreeNode> root = LoadTreeJson(input_path, true, base_dir);
  if (!root) {
    std::cerr << "Failed to load tree from " << input_path << "\n";
    return 1;
  }
  std::cout << "Loaded tree with root path \"" << root->path << "\" in "
            << load_timer.Seconds() << "s.\n";

  EffectiveBounds eff = ComputeEffectiveBounds(*root);
  std::cout << "Tree effective bounds: r_lower = " << eff.r_lower.ToString()
            << ", complete = " << (eff.complete ? "YES" : "NO") << "\n";

  if (eff.r_lower <= BigRat(0)) {
    std::cerr << "Error: Root effective r_lower is not positive ("
              << eff.r_lower.ToString() << "). Cannot export to Lean.\n";
    return 1;
  }

  // BFS traversal to assign topological row IDs (0 <= parent_id < child_id < N)
  std::vector<LeanRow> rows;
  std::queue<int> q;

  rows.push_back({
    .id = 0,
    .is_leaf = false,
    .rel_path = "",
    .child_ids = {-1, -1, -1, -1},
    .node = root.get()
  });
  q.push(0);
  int next_id = 1;

  while (!q.empty()) {
    int curr_idx = q.front();
    q.pop();

    const TreeNode *n = rows[curr_idx].node;
    bool can_prune = prune_at_cert &&
                     ((n->direct_cert.has_value() && n->direct_cert->r >= eff.r_lower) ||
                      (n->decomposed_cert.has_value() && n->decomposed_cert->r >= eff.r_lower));

    if (n->children.size() == 4 && !can_prune) {
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
        return 1;
      }
    }
  }

  std::cout << "Flattened tree into " << rows.size() << " Lean rows ("
            << (prune_at_cert ? "pruned" : "full") << ").\n";

  for (size_t i = 0; i < rows.size(); i++) {
    const auto &r = rows[i];
    if (r.node->decomposed_cert.has_value()) {
      std::cout << "Decomposed row " << i << ": path=\"" << r.node->path << "\", rel_path=\"" << r.rel_path << "\"\n";
    }
  }

  // Serializing into Lean packed format
  std::cout << "Writing Lean packed format to " << output_path << "...\n";
  std::ofstream out(output_path, std::ios::binary);
  if (!out.is_open()) {
    std::cerr << "Error: Failed to open output file " << output_path << "\n";
    return 1;
  }

  // Header: count, symmetryIndex(0), ZigzagRatString(table_r)
  out << rows.size() << ",0," << ZigzagRatString(eff.r_lower);

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
      const auto &dec = r.node->decomposed_cert.value();
      if (!dec.core_flock_axes.empty()) {
        // Flock Decomposed Certificate row (tag 3):
        // Format: tag(3), id, root(0), path_len, [path_digits], symmetryIndex,
        // [4 axes: annular_axis, complement_axes[0..2]], c, delta, r,
        // K, [K flock axes], defect0[0..2], D0, r_min, c_cone, c_core
        out << ",3," << r.id << ",0," << r.rel_path.size();
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

        // K flock axes
        out << "," << dec.core_flock_axes.size();
        for (size_t m = 0; m < dec.core_flock_axes.size(); m++) {
          WriteAxisPack(out, dec.core_flock_axes[m]);
        }

        // defect0[0..2], D0, r_min, c_cone, c_core
        out << "," << ZigzagRatString(dec.defect0[0])
            << "," << ZigzagRatString(dec.defect0[1])
            << "," << ZigzagRatString(dec.defect0[2])
            << "," << ZigzagRatString(dec.defect_D)
            << "," << ZigzagRatString(dec.r_min)
            << "," << ZigzagRatString(dec.c_cone)
            << "," << ZigzagRatString(dec.c_core);
      } else {
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
      WriteAxisPack(out, dec.inner_core_axis);

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
      }
    } else {
      LOG(FATAL) << "Encountered leaf node without certificate: " << r.node->path;
    }
  }

  out << "\n";
  out.close();

  std::cout << "Successfully generated " << output_path << " ("
            << std::filesystem::file_size(output_path) << " bytes).\n";
  return 0;
}
