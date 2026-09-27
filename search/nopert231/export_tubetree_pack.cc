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
        return 1;
      }
    }
  }

  std::cout << "Flattened tree into " << rows.size() << " Lean rows.\n";

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
      auto dec = r.node->decomposed_cert.value();
      TriangleQ tri = TriangleFromPath(r.node->path);
      std::string err;

      AxisCertificate coreAxis = dec.inner_core_axis;
      if (!dec.core_flock_axes.empty()) {
        coreAxis = dec.core_flock_axes[0];
      }

      // Audit annular axis on tri
      BigVecQ3 ctr_ann;
      BigRat del_ann;
      AxisCertificate ax_ann;
      ContactInfo c_ann[3] = {dec.annular_axis.contacts[0], dec.annular_axis.contacts[1], dec.annular_axis.contacts[2]};
      CHECK(Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat("1/1000")));
      dec.annular_axis = ax_ann;

      // Compute audited defect0 for annular axis
      BigRat max_def[3] = {BigRat(0), BigRat(0), BigRat(0)};
      BigVecQ3 edges_ann[3] = {
        Tube229::GetExactEdge(c_ann[0]),
        Tube229::GetExactEdge(c_ann[1]),
        Tube229::GetExactEdge(c_ann[2])
      };
      BigRat supp_err(6, 1000000000000000LL);
      for (int m = 0; m < 3; m++) {
        int sel = c_ann[m].vertex;
        BigVecQ3 v_sel = Tube229::VertexQ(sel);
        for (int k = 0; k < 20; k++) {
          bool tie = (k == sel) ||
                     (c_ann[m].mix == 1000 && sel == c_ann[m].edge_finish && k == c_ann[m].edge_start) ||
                     (c_ann[m].mix == 0 && sel == c_ann[m].edge_start2 && k == c_ann[m].edge_finish2);
          if (tie) continue;
          BigVecQ3 v_k = Tube229::VertexQ(k);
          BigVecQ3 delta = v_k - v_sel;
          BigVecQ3 cross = BigVecQ3::Cross(edges_ann[m], delta);
          BigRat max_s = BigVecQ3::Dot(tri.corners[0], cross);
          for (int c = 1; c < 3; c++) {
            BigRat s_c = BigVecQ3::Dot(tri.corners[c], cross);
            if (s_c > max_s) max_s = s_c;
          }
          BigRat supp_upper = max_s + supp_err;
          if (supp_upper > max_def[m]) max_def[m] = supp_upper;
        }
      }
      BigRat defect0[3];
      for (int m = 0; m < 3; m++) {
        BigRat d = max_def[m];
        if (d > 0) {
          BigInt num = d.Numerator();
          BigInt den = d.Denominator();
          BigInt scale(1000000000LL);
          BigInt c = (num * scale + den - 1) / den;
          defect0[m] = BigRat(c, scale);
        } else {
          defect0[m] = BigRat(0);
        }
      }
      BigVecQ3 coeff0 = BigVecQ3::Cross(edges_ann[1], edges_ann[2]);
      BigVecQ3 coeff1 = BigVecQ3::Cross(edges_ann[2], edges_ann[0]);
      BigVecQ3 coeff2 = BigVecQ3::Cross(edges_ann[0], edges_ann[1]);
      BigVecQ3 w_coeffs[3] = {coeff0, coeff1, coeff2};
      BigRat weight_upper[3];
      for (int m = 0; m < 3; m++) {
        BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
          if (val > w_max) w_max = val;
        }
        weight_upper[m] = w_max + supp_err;
      }
      BigRat D0 = weight_upper[0] * defect0[0] +
                  weight_upper[1] * defect0[1] +
                  weight_upper[2] * defect0[2];
      if (D0 > 0) {
        BigInt num = D0.Numerator();
        BigInt den = D0.Denominator();
        BigInt scale(1000000000LL);
        BigInt c = (num * scale + den - 1) / den;
        D0 = BigRat(c, scale);
      }
      if (D0 > dec.defect_D) {
        dec.defect_D = D0;
      }
      dec.defect0[0] = defect0[0];
      dec.defect0[1] = defect0[1];
      dec.defect0[2] = defect0[2];

      // Audit core axis on tri (must have 0 defect)
      BigVecQ3 ctr_core;
      BigRat del_core;
      AxisCertificate ax_core;
      ContactInfo c_core_ax[3] = {coreAxis.contacts[0], coreAxis.contacts[1], coreAxis.contacts[2]};
      if (!Tube229::AuditAxis(tri, c_core_ax, &ax_core, &ctr_core, &del_core, &err, BigRat(0))) {
        std::cerr << "FAILED AuditAxis core on row " << r.id << " path=" << r.node->path << ": " << err << "\n";
        abort();
      }
      coreAxis = ax_core;

      // Audit each complement axis on tri
      for (int a = 0; a < 3; a++) {
        AxisCertificate ax_comp;
        BigVecQ3 ctr_comp;
        BigRat del_comp;
        ContactInfo c_comp[3] = {dec.complement_axes[a].contacts[0], dec.complement_axes[a].contacts[1], dec.complement_axes[a].contacts[2]};
        CHECK(Tube229::AuditAxis(tri, c_comp, &ax_comp, &ctr_comp, &del_comp, &err, BigRat("1/1000")));
        dec.complement_axes[a] = ax_comp;
      }

      // True normalized centers (ctr_ann and ctr_core returned by AuditAxis are already evals/B)
      BigVecQ3 u0 = ctr_ann;
      BigVecQ3 v = ctr_core;

      BigRat dot = BigVecQ3::Dot(u0, v);
      BigRat u0_sq = BigVecQ3::Dot(u0, u0);
      BigRat lam = dot / u0_sq;
      BigVecQ3 w = v - u0 * lam;

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
          << "," << ZigzagRatString(lam)
          << "," << ZigzagRatString(w.x)
          << "," << ZigzagRatString(w.y)
          << "," << ZigzagRatString(w.z);
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
