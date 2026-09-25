// Standalone conversion tool: transforms tubecert229 JSON format into canonical tubetree229 format.

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unordered_map>
#include <memory>
#include <filesystem>
#include <format>

#include "rapidjson/document.h"
#include "rapidjson/filereadstream.h"
#include "tubetree229.h"

using namespace tubetree229;

struct RawNode {
  int id = -1;
  std::string kind;
  int depth = 0;
  std::vector<int> children;
  bool has_cert = false;
  TubeCertificate cert;
};

static bool ParseRawCertificate(const rapidjson::Value &val, TubeCertificate *out_cert) {
  if (!val.HasMember("certificate") || !val["certificate"].IsArray()) return false;
  const auto &c_arr = val["certificate"].GetArray();
  if (c_arr.Size() != 4) return false;

  out_cert->r = BigRat(val["r"].GetString());
  out_cert->c = BigRat(val["c"].GetString());
  out_cert->delta = BigRat(val["delta"].GetString());

  for (int a = 0; a < 4; a++) {
    const auto &ax_val = c_arr[a];
    AxisCertificate &axis = out_cert->axes[a];
    axis.B = BigRat(ax_val["B"].GetString());

    const auto &e_start = ax_val["edge_start"].GetArray();
    const auto &e_fin = ax_val["edge_finish"].GetArray();
    const auto &e_start2 = ax_val["edge_start2"].GetArray();
    const auto &e_fin2 = ax_val["edge_finish2"].GetArray();
    const auto &mix = ax_val["mix"].GetArray();
    const auto &supp = ax_val["support_index"].GetArray();
    const auto &wit = ax_val["nonzero_witness"].GetArray();

    for (int m = 0; m < 3; m++) {
      axis.contacts[m].vertex = supp[m].GetInt();
      axis.contacts[m].edge_start = e_start[m].GetInt();
      axis.contacts[m].edge_finish = e_fin[m].GetInt();
      axis.contacts[m].edge_start2 = e_start2[m].GetInt();
      axis.contacts[m].edge_finish2 = e_fin2[m].GetInt();
      axis.contacts[m].mix = mix[m].GetInt();
      axis.nonzero_witness[m] = wit[m].GetInt();
    }
  }
  return true;
}

static std::unique_ptr<TreeNode> BuildSubtree(
    int raw_id,
    const std::string &canonical_path,
    const std::unordered_map<int, RawNode> &raw_nodes,
    int64_t *out_total_nodes,
    int64_t *out_converted_certs) {

  auto node = std::make_unique<TreeNode>();
  node->path = canonical_path;
  (*out_total_nodes)++;

  auto it = raw_nodes.find(raw_id);
  if (it == raw_nodes.end()) {
    // Unresolved leaf
    return node;
  }

  const RawNode &raw = it->second;
  if (raw.has_cert) {
    node->direct_cert = raw.cert;
    node->direct_bounds.direct_r_lower = raw.cert.r;
    node->direct_bounds.direct_c_lower = raw.cert.c;
    (*out_converted_certs)++;
  }

  if (raw.kind == "view_split" && raw.children.size() == 4) {
    node->children.reserve(4);
    for (int i = 0; i < 4; i++) {
      std::string child_path = canonical_path + std::to_string(i);
      auto child = BuildSubtree(raw.children[i], child_path, raw_nodes, out_total_nodes, out_converted_certs);
      node->children.push_back(std::move(child));
    }
  }

  return node;
}

int main(int argc, char **argv) {
  std::string input_manifest = ".artifacts/nopert229/local-view-child0.json";
  std::string output_dir = ".artifacts/nopert229_tree";
  std::string root_path = "0";

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--input" && i + 1 < argc) {
      input_manifest = argv[++i];
    } else if (arg == "--output_dir" && i + 1 < argc) {
      output_dir = argv[++i];
    } else if (arg == "--root_path" && i + 1 < argc) {
      root_path = argv[++i];
    } else if (arg == "--help") {
      std::cout << "Usage: convert_tubecert229 [--input <manifest.json>] [--output_dir <dir>] [--root_path <0..3>]\n";
      return 0;
    }
  }

  std::cout << "=== Tubecert229 to Tubetree229 Converter ===\n";
  std::cout << "Input Manifest: " << input_manifest << "\n";
  std::cout << "Output Directory: " << output_dir << "\n";
  std::cout << "Root Path: \"" << root_path << "\"\n\n";

  if (!std::filesystem::exists(input_manifest)) {
    std::cerr << "Error: Input manifest file " << input_manifest << " does not exist!\n";
    return 1;
  }

  FILE *fp = fopen(input_manifest.c_str(), "rb");
  if (!fp) {
    std::cerr << "Failed to open " << input_manifest << "\n";
    return 1;
  }
  std::vector<char> buf(65536);
  rapidjson::FileReadStream is(fp, buf.data(), buf.size());
  rapidjson::Document doc;
  doc.ParseStream(is);
  fclose(fp);

  if (doc.HasParseError()) {
    std::cerr << "Failed to parse JSON manifest " << input_manifest << "\n";
    return 1;
  }

  std::filesystem::path manifest_dir = std::filesystem::path(input_manifest).parent_path();
  std::vector<std::string> chunk_files;
  if (doc.HasMember("chunks") && doc["chunks"].IsArray()) {
    for (const auto &c : doc["chunks"].GetArray()) {
      chunk_files.push_back((manifest_dir / c.GetString()).string());
    }
  }

  std::cout << "Found " << chunk_files.size() << " chunk file(s).\n";

  std::unordered_map<int, RawNode> raw_nodes;
  int64_t total_raw_parsed = 0;
  int64_t total_raw_certs = 0;

  for (const auto &chunk_path : chunk_files) {
    std::cout << "Loading " << chunk_path << "..." << std::flush;
    FILE *cfp = fopen(chunk_path.c_str(), "rb");
    if (!cfp) {
      std::cerr << "\nWarning: Could not open chunk " << chunk_path << "\n";
      continue;
    }
    rapidjson::FileReadStream cis(cfp, buf.data(), buf.size());
    rapidjson::Document cdoc;
    cdoc.ParseStream(cis);
    fclose(cfp);

    if (cdoc.HasParseError() || !cdoc.IsArray()) {
      std::cerr << "\nWarning: Failed to parse chunk JSON " << chunk_path << "\n";
      continue;
    }

    int chunk_nodes = 0;
    for (const auto &el : cdoc.GetArray()) {
      if (el.IsNull() || !el.IsObject()) continue;
      RawNode rn;
      rn.id = el["id"].GetInt();
      rn.kind = el["kind"].GetString();
      rn.depth = el.HasMember("depth") ? el["depth"].GetInt() : 0;
      if (el.HasMember("children") && el["children"].IsArray()) {
        for (const auto &ch : el["children"].GetArray()) {
          rn.children.push_back(ch.GetInt());
        }
      }
      if (rn.kind == "view_local") {
        if (ParseRawCertificate(el, &rn.cert)) {
          rn.has_cert = true;
          total_raw_certs++;
        }
      }
      raw_nodes[rn.id] = std::move(rn);
      chunk_nodes++;
      total_raw_parsed++;
    }
    std::cout << " (" << chunk_nodes << " nodes)\n";
  }

  std::cout << "\nParsed " << total_raw_parsed << " raw nodes, including " << total_raw_certs << " raw certificates.\n";

  // Build tree from root ID 0
  int64_t out_total_nodes = 0;
  int64_t out_converted_certs = 0;
  std::cout << "Constructing hierarchical canonical tree starting at path \"" << root_path << "\" (raw id=0)...\n";
  auto root = BuildSubtree(0, root_path, raw_nodes, &out_total_nodes, &out_converted_certs);

  std::filesystem::create_directories(output_dir);
  std::string output_file = SubtreeFilename(root_path, output_dir);

  std::cout << "Saving tree to " << output_file << "...\n";
  SaveTreeJson(*root, output_file, /*shallow=*/false);

  TreeStats stats = ComputeTreeStats(*root);
  EffectiveBounds eb = ComputeEffectiveBounds(*root);

  std::cout << "\n=== CONVERSION COMPLETE ===\n";
  std::cout << "Target File: " << output_file << "\n";
  std::cout << "Total Tree Nodes: " << stats.total_nodes << "\n";
  std::cout << "Leaf Nodes: " << stats.leaves << "\n";
  std::cout << "Direct Certificates: " << stats.direct_certificates << "\n";
  std::cout << "Max Tree Depth: " << stats.max_depth << "\n";
  std::cout << "Effective r_lower: " << eb.r_lower.ToString() << " (~" << eb.r_lower.ToDouble() << ")\n";
  std::cout << "Effective c_lower: " << eb.c_lower.ToString() << " (~" << eb.c_lower.ToDouble() << ")\n";
  std::cout << "Coverage Complete: " << (eb.complete ? "YES (PROVEN COMPLETE)" : "NO (CONTAINS UNRESOLVED CELLS)") << "\n";

  return 0;
}
