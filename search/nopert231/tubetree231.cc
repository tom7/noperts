#include "tubetree231.h"

#include <algorithm>
#include <cmath>
#include <filesystem>
#include <iostream>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "base/logging.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "rapidjson/document.h"
#include "rapidjson/error/en.h"
#include "rapidjson/rapidjson.h"
#include "util.h"
#include "yocto-math.h"

namespace tubetree231 {

void TriangleQ::Subdivide(TriangleQ children[4]) const {
  BigVecQ3 m01 = (corners[0] + corners[1]) / BigRat(2);
  BigVecQ3 m12 = (corners[1] + corners[2]) / BigRat(2);
  BigVecQ3 m20 = (corners[2] + corners[0]) / BigRat(2);
  children[0] = {corners[0], m01, m20};
  children[1] = {m01, corners[1], m12};
  children[2] = {m20, m12, corners[2]};
  children[3] = {m01, m12, m20};
}

TriangleQ GetRootWedge() {
  TriangleQ w;
  w.corners[0] = BigVecQ3(BigRat(1), BigRat(0), BigRat(0));
  w.corners[1] = BigVecQ3(BigRat(10, 41), BigRat(31, 41), BigRat(0));
  w.corners[2] = BigVecQ3(BigRat(0), BigRat(0), BigRat(1));
  return w;
}

TriangleQ TriangleFromPath(std::string_view path) {
  TriangleQ cur = GetRootWedge();
  for (char c : path) {
    if (c < '0' || c > '3') continue;
    int idx = c - '0';
    TriangleQ ch[4];
    cur.Subdivide(ch);
    cur = ch[idx];
  }
  return cur;
}

EffectiveBounds ComputeEffectiveBounds(const TreeNode &node) {
  EffectiveBounds b;
  b.r_lower = node.direct_bounds.direct_r_lower;
  b.r_upper = node.direct_bounds.direct_r_upper;
  b.c_lower = node.direct_bounds.direct_c_lower;
  b.c_upper = node.direct_bounds.direct_c_upper;

  if (node.direct_cert.has_value()) {
    if (node.direct_cert->r > b.r_lower) b.r_lower = node.direct_cert->r;
    if (node.direct_cert->c > b.c_lower) b.c_lower = node.direct_cert->c;
  }
  if (node.decomposed_cert.has_value()) {
    if (node.decomposed_cert->r > b.r_lower) b.r_lower = node.decomposed_cert->r;
    if (node.decomposed_cert->c_comp > b.c_lower) b.c_lower = node.decomposed_cert->c_comp;
  }
  b.complete = (b.r_lower > BigRat(0));

  if (node.children.size() == 4) {
    EffectiveBounds cb[4];
    bool all_children_complete = true;
    for (int i = 0; i < 4; i++) {
      CHECK(node.children[i] != nullptr);
      cb[i] = ComputeEffectiveBounds(*node.children[i]);
      if (!cb[i].complete) {
        all_children_complete = false;
      }
    }

    if (all_children_complete) {
      BigRat min_r_lower = cb[0].r_lower;
      BigRat max_r_upper = cb[0].r_upper;
      BigRat min_c_lower = cb[0].c_lower;
      BigRat max_c_upper = cb[0].c_upper;

      for (int i = 1; i < 4; i++) {
        if (cb[i].r_lower < min_r_lower) min_r_lower = cb[i].r_lower;
        if (cb[i].r_upper > max_r_upper) max_r_upper = cb[i].r_upper;
        if (cb[i].c_lower < min_c_lower) min_c_lower = cb[i].c_lower;
        if (cb[i].c_upper > max_c_upper) max_c_upper = cb[i].c_upper;
      }

      // The effective lower bound is the best between this triangle's direct certificate
      // and the collective minimum of its 4 children.
      if (min_r_lower > b.r_lower) b.r_lower = min_r_lower;
      if (min_c_lower > b.c_lower) b.c_lower = min_c_lower;

      // The effective upper bound tightens if children upper bound is smaller.
      if (b.r_upper == BigRat(0) || (max_r_upper > BigRat(0) && max_r_upper < b.r_upper)) {
        b.r_upper = max_r_upper;
      }
      if (b.c_upper == BigRat(0) || (max_c_upper > BigRat(0) && max_c_upper < b.c_upper)) {
        b.c_upper = max_c_upper;
      }
      b.complete = true;
    }
  }

  return b;
}

std::string SubtreeFilename(std::string_view path, std::string_view base_dir) {
  std::string fname = "tree_" + std::string(path) + ".json";
  if (base_dir.empty()) return fname;
  if (base_dir.back() == '/' || base_dir.back() == '\\') {
    return std::string(base_dir) + fname;
  }
  return std::string(base_dir) + "/" + fname;
}

static void SerializeContact(const ContactInfo &ct, std::string &out) {
  out += "{\"edge_start\": ";
  out += std::to_string(ct.edge_start);
  out += ", \"edge_finish\": ";
  out += std::to_string(ct.edge_finish);
  out += ", \"edge_start2\": ";
  out += std::to_string(ct.edge_start2);
  out += ", \"edge_finish2\": ";
  out += std::to_string(ct.edge_finish2);
  out += ", \"mix\": ";
  out += std::to_string(ct.mix);
  out += ", \"vertex\": ";
  out += std::to_string(ct.vertex);
  out += "}";
}

static void SerializeAxis(const AxisCertificate &ax, std::string &out) {
  out += "{\n\"B\": \"";
  out += ax.B.ToString();
  out += "\",\n\"nonzero_witness\": [";
  out += std::to_string(ax.nonzero_witness[0]);
  out += ", ";
  out += std::to_string(ax.nonzero_witness[1]);
  out += ", ";
  out += std::to_string(ax.nonzero_witness[2]);
  out += "],\n\"contacts\": [\n";

  for (int m = 0; m < 3; m++) {
    SerializeContact(ax.contacts[m], out);
    if (m + 1 < 3) out += ",\n";
    else out += "\n";
  }
  out += "]\n}";
}

static void SerializeDecomposedCertificate(const DecomposedCertificate &dc, std::string &out) {
  out += ",\n\"decomposed_certificate\": {\n";
  out += "\"r_min\": \"";
  out += dc.r_min.ToString();
  out += "\", \"r\": \"";
  out += dc.r.ToString();
  out += "\", \"c_cone\": \"";
  out += dc.c_cone.ToString();
  out += "\", \"delta\": \"";
  out += dc.delta.ToString();
  out += "\", \"defect_D\": \"";
  out += dc.defect_D.ToString();
  out += "\", \"c_comp\": \"";
  out += dc.c_comp.ToString();
  out += "\", \"c_core\": \"";
  out += dc.c_core.ToString();
  out += "\", \"lam\": \"";
  out += dc.lam.ToString();
  out += "\", \"symmetry_index\": ";
  out += std::to_string(dc.symmetry_index);
  out += ",\n\"defect0\": [\"";
  out += dc.defect0[0].ToString() + "\", \""
       + dc.defect0[1].ToString() + "\", \""
       + dc.defect0[2].ToString() + "\"]";
  out += ",\n\"w\": [\"";
  out += dc.w[0].ToString() + "\", \""
       + dc.w[1].ToString() + "\", \""
       + dc.w[2].ToString() + "\"]";
  out += ",\n\"inner_index\": [";
  out += std::to_string(dc.inner_index[0]) + ", "
       + std::to_string(dc.inner_index[1]) + ", "
       + std::to_string(dc.inner_index[2]);
  out += "],\n\"inner_core_axis\": ";
  SerializeAxis(dc.inner_core_axis, out);
  out += ",\n\"annular_axis\": ";
  SerializeAxis(dc.annular_axis, out);
  out += "\n";
  if (!dc.complement_axes.empty()) {
    out += ",\n\"complement_axes\": [\n";
    for (size_t i = 0; i < dc.complement_axes.size(); i++) {
      SerializeAxis(dc.complement_axes[i], out);
      if (i + 1 < dc.complement_axes.size()) out += ",\n";
      else out += "\n";
    }
    out += "]\n";
  }
  if (!dc.core_flock_axes.empty()) {
    out += ",\n\"core_flock_axes\": [\n";
    for (size_t i = 0; i < dc.core_flock_axes.size(); i++) {
      SerializeAxis(dc.core_flock_axes[i], out);
      if (i + 1 < dc.core_flock_axes.size()) out += ",\n";
      else out += "\n";
    }
    out += "]\n";
  }
  out += "}";
}

static void SerializeNode(const TreeNode &node, std::string &out, bool shallow) {
  out += "{\n\"path\": \"";
  out += node.path;
  out += "\"";

  // Direct bounds
  const auto &db = node.direct_bounds;
  if (db.direct_r_lower > BigRat(0) || db.direct_r_upper > BigRat(0) ||
      db.direct_c_lower > BigRat(0) || db.direct_c_upper > BigRat(0)) {
    out += ",\n\"direct_bounds\": {";
    bool first = true;
    auto append_bound = [&](const char *key, const BigRat &val) {
      if (val > BigRat(0)) {
        if (!first) out += ", ";
        first = false;
        out += "\"";
        out += key;
        out += "\": \"";
        out += val.ToString();
        out += "\"";
      }
    };
    append_bound("r_lower", db.direct_r_lower);
    append_bound("r_upper", db.direct_r_upper);
    append_bound("c_lower", db.direct_c_lower);
    append_bound("c_upper", db.direct_c_upper);
    out += "}";
  }

  // Direct certificate
  if (node.direct_cert.has_value()) {
    const auto &cert = *node.direct_cert;
    out += ",\n\"certificate\": {\n";
    out += "\"r\": \"";
    out += cert.r.ToString();
    out += "\", \"c\": \"";
    out += cert.c.ToString();
    out += "\", \"delta\": \"";
    out += cert.delta.ToString();
    out += "\", \"symmetry_index\": ";
    out += std::to_string(cert.symmetry_index);
    out += ",\n\"axes\": [\n";

    for (int a = 0; a < 4; a++) {
      SerializeAxis(cert.axes[a], out);
      if (a + 1 < 4) out += ",\n";
      else out += "\n";
    }
    out += "]\n}";
  }

  // Decomposed certificate
  if (node.decomposed_cert.has_value()) {
    SerializeDecomposedCertificate(*node.decomposed_cert, out);
  }

  // External reference flag
  if (node.external) {
    out += ",\n\"external\": true";
  } else if (!node.children.empty()) {
    if (shallow && node.external) {
      out += ",\n\"external\": true";
    } else {
      out += ",\n\"children\": [\n";
      for (size_t i = 0; i < node.children.size(); i++) {
        CHECK(node.children[i] != nullptr);
        SerializeNode(*node.children[i], out, shallow);
        if (i + 1 < node.children.size()) out += ",\n";
        else out += "\n";
      }
      out += "]";
    }
  }

  out += "\n}";
}

bool SaveTreeJson(const TreeNode &root, const std::string &filepath, bool shallow) {
  std::string s;
  s.reserve(4 * 1024 * 1024);
  s += "{\n\"format\": \"tubetree229_v1\",\n\"root_path\": \"";
  s += root.path;
  s += "\",\n\"tree\": ";
  SerializeNode(root, s, shallow);
  s += "\n}\n";

  return Util::WriteFile(filepath, s);
}

static inline int GetIntVal(const rapidjson::Value &v) {
  if (v.IsInt()) return v.GetInt();
  if (v.IsString()) return std::stoi(v.GetString());
  return 0;
}

static void DeserializeAxis(const rapidjson::Value &ax_val, AxisCertificate &ax) {
  if (!ax_val.IsObject()) return;
  if (ax_val.HasMember("B") && ax_val["B"].IsString()) {
    ax.B = BigRat(ax_val["B"].GetString());
  }
  if (ax_val.HasMember("nonzero_witness") && ax_val["nonzero_witness"].IsArray()) {
    const auto &nw = ax_val["nonzero_witness"].GetArray();
    for (rapidjson::SizeType i = 0; i < nw.Size() && i < 3; i++) {
      ax.nonzero_witness[i] = GetIntVal(nw[i]);
    }
  }
  if (ax_val.HasMember("contacts") && ax_val["contacts"].IsArray()) {
    const auto &ct_arr = ax_val["contacts"].GetArray();
    for (rapidjson::SizeType m = 0; m < ct_arr.Size() && m < 3; m++) {
      const auto &ct_val = ct_arr[m];
      auto &ct = ax.contacts[m];
      if (ct_val.HasMember("edge_start")) ct.edge_start = GetIntVal(ct_val["edge_start"]);
      if (ct_val.HasMember("edge_finish")) ct.edge_finish = GetIntVal(ct_val["edge_finish"]);
      if (ct_val.HasMember("edge_start2")) ct.edge_start2 = GetIntVal(ct_val["edge_start2"]);
      if (ct_val.HasMember("edge_finish2")) ct.edge_finish2 = GetIntVal(ct_val["edge_finish2"]);
      if (ct_val.HasMember("mix")) ct.mix = GetIntVal(ct_val["mix"]);
      if (ct_val.HasMember("vertex")) ct.vertex = GetIntVal(ct_val["vertex"]);
    }
  }
}

static std::unique_ptr<TreeNode> DeserializeNode(
    const rapidjson::Value &val,
    bool load_external,
    std::string_view base_dir) {
  if (!val.IsObject()) return nullptr;

  auto node = std::make_unique<TreeNode>();
  if (val.HasMember("path") && val["path"].IsString()) {
    node->path = val["path"].GetString();
  }

  // Direct bounds
  if (val.HasMember("direct_bounds") && val["direct_bounds"].IsObject()) {
    const auto &db = val["direct_bounds"];
    if (db.HasMember("r_lower") && db["r_lower"].IsString()) {
      node->direct_bounds.direct_r_lower = BigRat(db["r_lower"].GetString());
    }
    if (db.HasMember("r_upper") && db["r_upper"].IsString()) {
      node->direct_bounds.direct_r_upper = BigRat(db["r_upper"].GetString());
    }
    if (db.HasMember("c_lower") && db["c_lower"].IsString()) {
      node->direct_bounds.direct_c_lower = BigRat(db["c_lower"].GetString());
    }
    if (db.HasMember("c_upper") && db["c_upper"].IsString()) {
      node->direct_bounds.direct_c_upper = BigRat(db["c_upper"].GetString());
    }
  }

  // Direct certificate
  if (val.HasMember("certificate") && val["certificate"].IsObject()) {
    const auto &cobj = val["certificate"];
    TubeCertificate cert;
    if (cobj.HasMember("r") && cobj["r"].IsString()) cert.r = BigRat(cobj["r"].GetString());
    if (cobj.HasMember("c") && cobj["c"].IsString()) cert.c = BigRat(cobj["c"].GetString());
    if (cobj.HasMember("delta") && cobj["delta"].IsString()) cert.delta = BigRat(cobj["delta"].GetString());
    if (cobj.HasMember("symmetry_index")) cert.symmetry_index = GetIntVal(cobj["symmetry_index"]);

    if (cobj.HasMember("axes") && cobj["axes"].IsArray()) {
      const auto &ax_arr = cobj["axes"].GetArray();
      for (rapidjson::SizeType a = 0; a < ax_arr.Size() && a < 4; a++) {
        DeserializeAxis(ax_arr[a], cert.axes[a]);
      }
    }
    node->direct_cert = std::move(cert);
    if (node->direct_bounds.direct_r_lower == BigRat(0)) {
      node->direct_bounds.direct_r_lower = node->direct_cert->r;
    }
    if (node->direct_bounds.direct_c_lower == BigRat(0)) {
      node->direct_bounds.direct_c_lower = node->direct_cert->c;
    }
  }

  // Decomposed certificate
  if (val.HasMember("decomposed_certificate") && val["decomposed_certificate"].IsObject()) {
    const auto &dobj = val["decomposed_certificate"];
    DecomposedCertificate dc;
    if (dobj.HasMember("r_min") && dobj["r_min"].IsString()) dc.r_min = BigRat(dobj["r_min"].GetString());
    if (dobj.HasMember("r") && dobj["r"].IsString()) dc.r = BigRat(dobj["r"].GetString());
    if (dobj.HasMember("c_cone") && dobj["c_cone"].IsString()) dc.c_cone = BigRat(dobj["c_cone"].GetString());
    if (dobj.HasMember("delta") && dobj["delta"].IsString()) dc.delta = BigRat(dobj["delta"].GetString());
    if (dobj.HasMember("defect_D") && dobj["defect_D"].IsString()) dc.defect_D = BigRat(dobj["defect_D"].GetString());
    if (dobj.HasMember("c_comp") && dobj["c_comp"].IsString()) dc.c_comp = BigRat(dobj["c_comp"].GetString());
    if (dobj.HasMember("c_core") && dobj["c_core"].IsString()) dc.c_core = BigRat(dobj["c_core"].GetString());
    if (dobj.HasMember("lam") && dobj["lam"].IsString()) dc.lam = BigRat(dobj["lam"].GetString());
    if (dobj.HasMember("symmetry_index")) dc.symmetry_index = GetIntVal(dobj["symmetry_index"]);

    if (dobj.HasMember("defect0") && dobj["defect0"].IsArray()) {
      const auto &d_arr = dobj["defect0"].GetArray();
      for (rapidjson::SizeType i = 0; i < d_arr.Size() && i < 3; i++) {
        if (d_arr[i].IsString()) dc.defect0[i] = BigRat(d_arr[i].GetString());
      }
    }
    if (dobj.HasMember("w") && dobj["w"].IsArray()) {
      const auto &w_arr = dobj["w"].GetArray();
      for (rapidjson::SizeType i = 0; i < w_arr.Size() && i < 3; i++) {
        if (w_arr[i].IsString()) dc.w[i] = BigRat(w_arr[i].GetString());
      }
    }

    if (dobj.HasMember("inner_index") && dobj["inner_index"].IsArray()) {
      const auto &idx_arr = dobj["inner_index"].GetArray();
      for (rapidjson::SizeType i = 0; i < idx_arr.Size() && i < 3; i++) {
        dc.inner_index[i] = GetIntVal(idx_arr[i]);
      }
    }
    if (dobj.HasMember("inner_core_axis") && dobj["inner_core_axis"].IsObject()) {
      DeserializeAxis(dobj["inner_core_axis"], dc.inner_core_axis);
    }
    if (dobj.HasMember("annular_axis") && dobj["annular_axis"].IsObject()) {
      DeserializeAxis(dobj["annular_axis"], dc.annular_axis);
    }
    if (dobj.HasMember("complement_axes") && dobj["complement_axes"].IsArray()) {
      const auto &comp_arr = dobj["complement_axes"].GetArray();
      dc.complement_axes.resize(comp_arr.Size());
      for (rapidjson::SizeType i = 0; i < comp_arr.Size(); i++) {
        DeserializeAxis(comp_arr[i], dc.complement_axes[i]);
      }
    }
    if (dobj.HasMember("core_flock_axes") && dobj["core_flock_axes"].IsArray()) {
      const auto &flock_arr = dobj["core_flock_axes"].GetArray();
      dc.core_flock_axes.resize(flock_arr.Size());
      for (rapidjson::SizeType i = 0; i < flock_arr.Size(); i++) {
        DeserializeAxis(flock_arr[i], dc.core_flock_axes[i]);
      }
    }

    node->decomposed_cert = std::move(dc);
    if (node->direct_bounds.direct_r_lower == BigRat(0)) {
      node->direct_bounds.direct_r_lower = node->decomposed_cert->r;
    }
    if (node->direct_bounds.direct_c_lower == BigRat(0)) {
      node->direct_bounds.direct_c_lower = node->decomposed_cert->c_comp;
    }
  }

  // External reference
  if (val.HasMember("external") && val["external"].IsBool() && val["external"].GetBool()) {
    node->external = true;
    if (load_external) {
      std::string ext_file = SubtreeFilename(node->path, base_dir);
      auto ext_root = LoadTreeJson(ext_file, load_external, base_dir);
      if (ext_root && ext_root->path == node->path) {
        node->children = std::move(ext_root->children);
        node->external = false;
      }
    }
  } else if (val.HasMember("children") && val["children"].IsArray()) {
    const auto &c_arr = val["children"].GetArray();
    node->children.reserve(c_arr.Size());
    for (const auto &child_val : c_arr) {
      auto child = DeserializeNode(child_val, load_external, base_dir);
      if (child) {
        node->children.push_back(std::move(child));
      }
    }
  }

  return node;
}

std::unique_ptr<TreeNode> LoadTreeJson(
    const std::string &filepath,
    bool load_external,
    std::string_view base_dir) {
  std::string content = Util::ReadFile(filepath);
  if (content.empty()) return nullptr;

  rapidjson::Document doc;
  doc.Parse(content.c_str());
  if (doc.HasParseError()) {
    std::cerr << "JSON parse error in " << filepath << ": "
              << rapidjson::GetParseError_En(doc.GetParseError()) << "\n";
    return nullptr;
  }

  if (doc.HasMember("tree") && doc["tree"].IsObject()) {
    return DeserializeNode(doc["tree"], load_external, base_dir);
  } else if (doc.IsObject()) {
    return DeserializeNode(doc, load_external, base_dir);
  }

  return nullptr;
}

bool DetachSubtreeToFile(TreeNode *node, const std::string &base_dir) {
  CHECK(node != nullptr);
  if (node->children.empty()) return false;

  std::string fname = SubtreeFilename(node->path, base_dir);
  if (!SaveTreeJson(*node, fname, /*shallow=*/true)) {
    return false;
  }

  node->children.clear();
  node->external = true;
  return true;
}

bool AttachSubtreeFromFile(TreeNode *node, const std::string &base_dir) {
  CHECK(node != nullptr);
  std::string fname = SubtreeFilename(node->path, base_dir);
  auto ext = LoadTreeJson(fname, /*load_external=*/false, base_dir);
  if (!ext || ext->path != node->path) return false;

  node->children = std::move(ext->children);
  node->external = false;
  return true;
}

static void AccumulateStats(const TreeNode &node, TreeStats &stats, int cur_depth) {
  stats.total_nodes++;
  if (cur_depth > stats.max_depth) stats.max_depth = cur_depth;
  if (node.direct_cert.has_value()) stats.direct_certificates++;
  if (node.decomposed_cert.has_value()) stats.decomposed_certificates++;

  if (node.external) {
    stats.external_refs++;
    stats.split_nodes++;
  } else if (node.children.empty()) {
    stats.leaves++;
  } else {
    stats.split_nodes++;
    for (const auto &child : node.children) {
      if (child) AccumulateStats(*child, stats, cur_depth + 1);
    }
  }
}

TreeStats ComputeTreeStats(const TreeNode &root) {
  TreeStats stats;
  AccumulateStats(root, stats, root.depth());
  return stats;
}

// TubeAtlas implementations

std::unique_ptr<TubeAtlas::FastNode> TubeAtlas::BuildFastNode(const TreeNode &node) {
  auto fn = std::make_unique<TubeAtlas::FastNode>();
  fn->path = node.path;
  fn->direct_r_rat = node.direct_bounds.direct_r_lower;
  if (node.direct_cert.has_value() && node.direct_cert->r > fn->direct_r_rat) {
    fn->direct_r_rat = node.direct_cert->r;
  }
  fn->direct_r_lower = fn->direct_r_rat.ToDouble();
  fn->is_leaf = node.children.empty() && !node.external;

  for (const auto &child : node.children) {
    if (child && !child->path.empty()) {
      int idx = child->path.back() - '0';
      if (idx >= 0 && idx < 4) {
        fn->children[idx] = BuildFastNode(*child);
      }
    }
  }
  return fn;
}

void TubeAtlas::ComputeFastEffectiveBounds(FastNode *node) {
  if (!node) return;

  bool has_4_children = true;
  for (int i = 0; i < 4; i++) {
    if (!node->children[i]) {
      has_4_children = false;
      break;
    }
    ComputeFastEffectiveBounds(node->children[i].get());
  }

  if (has_4_children) {
    bool all_children_complete = true;
    BigRat min_child_rat = node->children[0]->effective_r_rat;
    for (int i = 0; i < 4; i++) {
      if (node->children[i]->effective_r_rat <= BigRat(0)) {
        all_children_complete = false;
        break;
      }
      if (node->children[i]->effective_r_rat < min_child_rat) {
        min_child_rat = node->children[i]->effective_r_rat;
      }
    }

    if (all_children_complete) {
      if (min_child_rat > node->direct_r_rat) {
        node->effective_r_rat = min_child_rat;
      } else {
        node->effective_r_rat = node->direct_r_rat;
      }
    } else {
      node->effective_r_rat = node->direct_r_rat;
    }
  } else {
    node->effective_r_rat = node->direct_r_rat;
  }
  node->effective_r_lower = node->effective_r_rat.ToDouble();
}

int TubeAtlas::LoadFromDir(const std::string &base_dir) {
  int count = 0;
  for (int sw = 0; sw < 4; sw++) {
    std::string path = base_dir + "/tree_" + std::to_string(sw) + ".json";
    if (std::filesystem::exists(path)) {
      if (LoadTree(sw, path)) {
        count++;
      }
    }
  }
  return count;
}

bool TubeAtlas::LoadTree(int subwedge, const std::string &filepath) {
  if (subwedge < 0 || subwedge > 3) return false;
  auto root = LoadTreeJson(filepath, /*load_external=*/false);
  if (!root) return false;

  auto fast_root = BuildFastNode(*root);
  ComputeFastEffectiveBounds(fast_root.get());
  roots_[subwedge] = std::move(fast_root);
  {
    std::lock_guard<std::mutex> lock(cache_mutex_);
    certified_cache_built_ = false;
    certified_cache_.clear();
  }
  return true;
}

const TubeAtlas::FastNode *TubeAtlas::FindNode(std::string_view path) const {
  if (path.empty()) return nullptr;
  int sw = path[0] - '0';
  if (sw < 0 || sw > 3 || !roots_[sw]) return nullptr;

  const FastNode *curr = roots_[sw].get();
  for (size_t i = 1; i < path.size(); i++) {
    int c = path[i] - '0';
    if (c < 0 || c > 3) break;
    if (curr->children[c]) {
      curr = curr->children[c].get();
    } else {
      break;
    }
  }
  return curr;
}

double TubeAtlas::GetSafeRadiusForPath(std::string_view path) const {
  const FastNode *node = FindNode(path);
  if (!node) return 0.0;
  return node->effective_r_lower;
}

BigRat TubeAtlas::GetSafeRadiusRatForPath(std::string_view path) const {
  const FastNode *node = FindNode(path);
  if (!node) return BigRat(0);
  return node->effective_r_rat;
}

double TubeAtlas::GetSafeRadiusForTriangle(const vec3 corners[3], int max_depth) const {
  vec3 w0 = {1.0, 0.0, 0.0};
  vec3 w1 = {10.0 / 41.0, 31.0 / 41.0, 0.0};
  vec3 w2 = {0.0, 0.0, 1.0};
  vec3 cur_corners[3] = {w0, w1, w2};

  vec3 target_cent = (corners[0] + corners[1] + corners[2]) * (1.0 / 3.0);
  std::string path;

  for (int d = 0; d < max_depth; d++) {
    double diff = yocto::length(cur_corners[0] - corners[0]) +
                  yocto::length(cur_corners[1] - corners[1]) +
                  yocto::length(cur_corners[2] - corners[2]);
    if (diff < 1e-7) break;

    vec3 m01 = (cur_corners[0] + cur_corners[1]) * 0.5;
    vec3 m12 = (cur_corners[1] + cur_corners[2]) * 0.5;
    vec3 m20 = (cur_corners[2] + cur_corners[0]) * 0.5;

    vec3 subs[4][3] = {
      {cur_corners[0], m01, m20},
      {m01, cur_corners[1], m12},
      {m20, m12, cur_corners[2]},
      {m01, m12, m20}
    };

    int best_c = -1;
    double best_dist = 1e30;

    for (int c = 0; c < 4; c++) {
      vec3 cp = yocto::cross(subs[c][1], subs[c][2]);
      double det = yocto::dot(subs[c][0], cp);
      if (std::abs(det) > 1e-15) {
        double s = (det > 0.0) ? 1.0 : -1.0;
        double d0 = s * yocto::dot(target_cent, cp);
        double d1 = s * yocto::dot(target_cent, yocto::cross(subs[c][2], subs[c][0]));
        double d2 = s * yocto::dot(target_cent, yocto::cross(subs[c][0], subs[c][1]));
        if (d0 >= -1e-11 && d1 >= -1e-11 && d2 >= -1e-11) {
          best_c = c;
          break;
        }
      }
      vec3 sub_cent = (subs[c][0] + subs[c][1] + subs[c][2]) * (1.0 / 3.0);
      vec3 cross_prod = yocto::cross(sub_cent, target_cent);
      double dist = yocto::dot(cross_prod, cross_prod);
      if (dist < best_dist) {
        best_dist = dist;
        best_c = c;
      }
    }

    if (best_c >= 0) {
      path.push_back('0' + best_c);
      cur_corners[0] = subs[best_c][0];
      cur_corners[1] = subs[best_c][1];
      cur_corners[2] = subs[best_c][2];
    } else {
      break;
    }
  }

  return GetSafeRadiusForPath(path);
}

static inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

void TubeAtlas::EnsureCertifiedCache() const {
  std::lock_guard<std::mutex> lock(cache_mutex_);
  if (certified_cache_built_) return;
  certified_cache_.clear();

  auto collect = [&](auto &self, const FastNode *node, int sw) -> void {
    if (!node) return;
    if (node->direct_r_lower > 0.0 || node->effective_r_lower > 0.0) {
      TriangleQ tq = TriangleFromPath(node->path);
      vec3 c0 = ToDouble(tq.corners[0]);
      vec3 c1 = ToDouble(tq.corners[1]);
      vec3 c2 = ToDouble(tq.corners[2]);
      vec3 cent = (c0 + c1 + c2) * (1.0 / 3.0);
      double len = yocto::length(cent);
      if (len > 1e-12) cent = cent * (1.0 / len);
      certified_cache_.push_back({node, cent, {c0, c1, c2}, sw});
    }
    for (int i = 0; i < 4; i++) {
      if (node->children[i]) {
        self(self, node->children[i].get(), sw);
      }
    }
  };

  for (int sw = 0; sw < 4; sw++) {
    if (roots_[sw]) {
      collect(collect, roots_[sw].get(), sw);
    }
  }

  certified_cache_built_ = true;
}

std::optional<NearestCertifiedNodeResult> FindNearestCertifiedNode(
    const TreeNode &root, const vec3 &direction) {
  double len = yocto::length(direction);
  if (len < 1e-12) return std::nullopt;
  vec3 q = direction * (1.0 / len);

  const TreeNode *best_contained = nullptr;
  double best_contained_r = -1.0;
  vec3 best_contained_cent{0, 0, 0};

  const TreeNode *best_nearest = nullptr;
  double best_dot = -2.0;
  vec3 best_nearest_cent{0, 0, 0};

  auto search = [&](auto &self, const TreeNode &node) -> void {
    double r = node.direct_bounds.direct_r_lower.ToDouble();
    if (r > 0.0) {
      TriangleQ tq = node.GetTriangle();
      vec3 c0 = ToDouble(tq.corners[0]);
      vec3 c1 = ToDouble(tq.corners[1]);
      vec3 c2 = ToDouble(tq.corners[2]);
      vec3 cent = (c0 + c1 + c2) * (1.0 / 3.0);
      double clen = yocto::length(cent);
      if (clen > 1e-12) cent = cent * (1.0 / clen);

      vec3 cp0 = yocto::cross(c0, c1);
      vec3 cp1 = yocto::cross(c1, c2);
      vec3 cp2 = yocto::cross(c2, c0);
      double det = yocto::dot(c0, yocto::cross(c1, c2));
      if (std::abs(det) > 1e-15) {
        double s = (det > 0.0) ? 1.0 : -1.0;
        bool inside = (s * yocto::dot(q, cp0) >= -1e-11) &&
                      (s * yocto::dot(q, cp1) >= -1e-11) &&
                      (s * yocto::dot(q, cp2) >= -1e-11);
        if (inside && r > 0.0 && (r > best_contained_r ||
            (r == best_contained_r && (!best_contained || node.path.size() > best_contained->path.size())))) {
          best_contained_r = r;
          best_contained = &node;
          best_contained_cent = cent;
        }
      }

      double dot = yocto::dot(q, cent);
      if (dot > best_dot) {
        best_dot = dot;
        best_nearest = &node;
        best_nearest_cent = cent;
      }
    }
    for (const auto &c : node.children) {
      if (c) self(self, *c);
    }
  };

  search(search, root);

  if (best_contained) {
    NearestCertifiedNodeResult res;
    res.path = best_contained->path;
    res.direct_r_lower = best_contained->direct_bounds.direct_r_lower.ToDouble();
    res.effective_r_lower = res.direct_r_lower;
    res.direct_r_rat = best_contained->direct_bounds.direct_r_lower;
    res.effective_r_rat = res.direct_r_rat;
    res.angular_distance = 0.0;
    res.triangle_center = best_contained_cent;
    res.contains_direction = true;
    return res;
  }

  if (best_nearest) {
    NearestCertifiedNodeResult res;
    res.path = best_nearest->path;
    res.direct_r_lower = best_nearest->direct_bounds.direct_r_lower.ToDouble();
    res.effective_r_lower = res.direct_r_lower;
    res.direct_r_rat = best_nearest->direct_bounds.direct_r_lower;
    res.effective_r_rat = res.direct_r_rat;
    double clamped_dot = std::max(-1.0, std::min(1.0, best_dot));
    res.angular_distance = std::acos(clamped_dot);
    res.triangle_center = best_nearest_cent;
    res.contains_direction = false;
    return res;
  }

  return std::nullopt;
}

static int CountLeavesInNode(const TreeNode &node) {
  if (node.is_leaf()) return 1;
  int count = 0;
  for (const auto &child : node.children) {
    if (child) count += CountLeavesInNode(*child);
  }
  return count;
}

static bool CheckFullyCertifiedInNode(const TreeNode &node) {
  if (node.is_leaf()) {
    return node.has_certificate() && node.GetCertifiedRadius() > BigRat(0);
  }
  for (const auto &child : node.children) {
    if (!child || !CheckFullyCertifiedInNode(*child)) return false;
  }
  return true;
}

int CodeTree::TotalLeaves() const {
  int total = 0;
  for (const auto &ct : triangles) {
    if (ct.root) total += CountLeavesInNode(*ct.root);
  }
  return total;
}

bool CodeTree::IsFullyCertified() const {
  if (triangles.empty()) return false;
  for (const auto &ct : triangles) {
    if (!ct.root || !CheckFullyCertifiedInNode(*ct.root)) return false;
  }
  return true;
}

bool SaveCodeTreeJson(const CodeTree &code_tree, const std::string &filepath) {
  std::string s;
  s.reserve(4 * 1024 * 1024);
  s += "{\n\"format\": \"tubetree229_code_v1\",\n";
  s += "\"code_id\": " + std::to_string(code_tree.code_id) + ",\n";
  s += "\"code_hex\": \"" + code_tree.code_hex + "\",\n";
  s += "\"num_triangles\": " + std::to_string(code_tree.triangles.size()) + ",\n";
  s += "\"triangles\": [\n";

  for (size_t t = 0; t < code_tree.triangles.size(); t++) {
    const auto &ct = code_tree.triangles[t];
    s += "{\n";
    s += "\"triangle_index\": " + std::to_string(ct.triangle_index) + ",\n";
    s += "\"corners\": [\n";
    for (int k = 0; k < 3; k++) {
      s += "  {\"x\": \"" + ct.triangle.corners[k].x.ToString() +
           "\", \"y\": \"" + ct.triangle.corners[k].y.ToString() +
           "\", \"z\": \"" + ct.triangle.corners[k].z.ToString() + "\"}";
      if (k + 1 < 3) s += ",\n";
      else s += "\n";
    }
    s += "],\n";
    s += "\"tree\": ";
    if (ct.root) {
      SerializeNode(*ct.root, s, false);
    } else {
      s += "null";
    }
    s += "\n}";
    if (t + 1 < code_tree.triangles.size()) s += ",\n";
    else s += "\n";
  }

  s += "]\n}\n";
  return Util::WriteFile(filepath, s);
}

std::unique_ptr<CodeTree> LoadCodeTreeJson(const std::string &filepath) {
  std::string content = Util::ReadFile(filepath);
  if (content.empty()) return nullptr;

  rapidjson::Document doc;
  doc.Parse(content.c_str());
  if (doc.HasParseError() || !doc.IsObject()) return nullptr;

  auto code_tree = std::make_unique<CodeTree>();
  if (doc.HasMember("code_id") && doc["code_id"].IsInt()) {
    code_tree->code_id = doc["code_id"].GetInt();
  }
  if (doc.HasMember("code_hex") && doc["code_hex"].IsString()) {
    code_tree->code_hex = doc["code_hex"].GetString();
  }

  if (doc.HasMember("triangles") && doc["triangles"].IsArray()) {
    const auto &tri_arr = doc["triangles"].GetArray();
    for (rapidjson::SizeType t = 0; t < tri_arr.Size(); t++) {
      const auto &tval = tri_arr[t];
      CodeTriangleTree ct;
      if (tval.HasMember("triangle_index") && tval["triangle_index"].IsInt()) {
        ct.triangle_index = tval["triangle_index"].GetInt();
      }
      if (tval.HasMember("corners") && tval["corners"].IsArray()) {
        const auto &c_arr = tval["corners"].GetArray();
        for (int k = 0; k < 3 && k < (int)c_arr.Size(); k++) {
          ct.triangle.corners[k] = BigVecQ3(
              c_arr[k]["x"].GetString(),
              c_arr[k]["y"].GetString(),
              c_arr[k]["z"].GetString());
        }
      }
      if (tval.HasMember("tree") && tval["tree"].IsObject()) {
        ct.root = DeserializeNode(tval["tree"], false, "");
      }
      code_tree->triangles.push_back(std::move(ct));
    }
  }

  return code_tree;
}

} // namespace tubetree231

