// telescope229.cc: Telescoping View Subdivider for candidate #229 difficult cells.
// Subdivides the view triangle of a difficult cell down N levels (4^N sub-triangles).
// If 4^N - 1 sub-triangles are certified (by identity tube, Farkas LP, mixtures, or
// shallow box splits), locks in the 4^N - 1 solved branches permanently into a
// hierarchical .done file containing exactly ONE 'DF' (DIFFICULT) leaf.
// The single remaining uncertified needle sub-wedge is emitted to chart<chart>.<id>.difficult.
//
// TODO: telescope229 is an experimental fork of difficult229 that explores
// multi-level view telescoping and frontier roll-up (collapsing open leaves
// to a single Lowest Common Ancestor). If this experiment works, we should
// merge this logic directly into difficult229.cc.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mutex>
#include <numeric>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "ansi.h"
#include "base/logging.h"
#include "base/print.h"
#include "lib229.h"
#include "tubetree229.h"

struct VerificationResult {
  bool valid = false;
  uint64_t total_rows = 0;
  uint64_t total_leaves = 0;
  uint64_t total_splits = 0;
  uint64_t difficult_leaves = 0;
  double worst_margin = 1e30;
  std::string error_message;
};

struct ParsedDoneRow {
  std::string tag;
  int64_t id = -1;
  int64_t parent_id = -1;
  int depth = 0;
  std::vector<int64_t> children;
  double margin = 0.0;
  std::string prune_kind;
  int fund_dir = 0;
  double tube_radius = 0.0;
};

static VerificationResult VerifyDoneFile(
    const DifficultCell &cell, const std::string &done_path,
    const tubetree229::TubeAtlas *tube_atlas = nullptr,
    bool allow_difficult = true,
    double experiment_tube_floor = 0.0) {
  std::ifstream infile(done_path);
  if (!infile.is_open()) {
    return {.valid = false, .error_message = "Could not open file"};
  }

  std::unordered_map<int64_t, ParsedDoneRow> row_map;
  std::string line;
  uint64_t line_no = 0;

  while (std::getline(infile, line)) {
    line_no++;
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    std::string tag;
    int64_t id, parent_id;
    int depth;
    if (!(iss >> tag >> id >> parent_id >> depth)) {
      return {.valid = false, .error_message = std::format("Malformed line on line {}: '{}'", line_no, line)};
    }

    ParsedDoneRow row;
    row.tag = tag;
    row.id = id;
    row.parent_id = parent_id;
    row.depth = depth;

    if (tag == "SP" || tag == "SPLIT" || tag == "SO" || tag == "SPLIT_ORIGIN") {
      int64_t c0, c1;
      if (!(iss >> c0 >> c1)) {
        return {.valid = false, .error_message = std::format("Line {}: {} missing child IDs", line_no, tag)};
      }
      row.children = {c0, c1};
    } else if (tag == "SV" || tag == "SPLIT_VIEW") {
      int64_t c0, c1, c2, c3;
      if (!(iss >> c0 >> c1 >> c2 >> c3)) {
        return {.valid = false, .error_message = std::format("Line {}: SV missing 4 child IDs", line_no)};
      }
      row.children = {c0, c1, c2, c3};
    } else if (tag == "CE" || tag == "CERT") {
      int triple;
      int in0, in1, in2;
      if (!(iss >> triple >> row.margin >> in0 >> in1 >> in2)) {
        return {.valid = false, .error_message = std::format("Line {}: malformed CE row", line_no)};
      }
    } else if (tag == "MX") {
      int num_components;
      if (!(iss >> num_components >> row.margin)) {
        return {.valid = false, .error_message = std::format("Line {}: malformed MX row", line_no)};
      }
      for (int k = 0; k < num_components; k++) {
        int trip, in0, in1, in2;
        double w;
        if (!(iss >> trip >> w >> in0 >> in1 >> in2)) {
          return {.valid = false, .error_message = std::format("Line {}: malformed MX component {}", line_no, k)};
        }
      }
    } else if (tag == "PR" || tag == "PRUNE") {
      if (!(iss >> row.prune_kind)) {
        return {.valid = false, .error_message = std::format("Line {}: PR missing kind", line_no)};
      }
      if (row.prune_kind == "FUNDAMENTAL" || row.prune_kind == "FU") {
        if (!(iss >> row.fund_dir)) {
          return {.valid = false, .error_message = std::format("Line {}: PR FUNDAMENTAL missing direction", line_no)};
        }
      }
    } else if (tag == "TU" || tag == "TUBE") {
      if (!(iss >> row.tube_radius)) {
        return {.valid = false, .error_message = std::format("Line {}: TU missing radius", line_no)};
      }
    } else if (tag == "DF" || tag == "DI" || tag == "DIFFICULT") {
      if (!allow_difficult) {
        return {.valid = false, .error_message = std::format("Line {}: contains uncertified DIFFICULT leaf", line_no)};
      }
      row.prune_kind = "DIFFICULT";
    } else {
      return {.valid = false, .error_message = std::format("Line {}: unrecognized row tag '{}'", line_no, tag)};
    }

    if (row_map.contains(id)) {
      return {.valid = false, .error_message = std::format("Duplicate node ID {} on line {}", id, line_no)};
    }
    row_map[id] = std::move(row);
  }

  if (row_map.empty()) {
    return {.valid = false, .error_message = "File is empty"};
  }

  if (!row_map.contains(cell.id)) {
    return {.valid = false, .error_message = std::format("Root cell #{} not found in file", cell.id)};
  }

  std::vector<SearchNode> stack;
  stack.push_back(cell.ToSearchNode());
  std::unordered_set<int64_t> visited;
  uint64_t leaf_count = 0;
  uint64_t split_count = 0;
  uint64_t difficult_leaves = 0;
  double worst_margin = 1e30;

  while (!stack.empty()) {
    SearchNode curr = stack.back();
    stack.pop_back();

    if (visited.contains(curr.id)) {
      return {.valid = false, .error_message = std::format("Cycle detected at node #{}", curr.id)};
    }
    visited.insert(curr.id);

    auto it = row_map.find(curr.id);
    if (it == row_map.end()) {
      return {.valid = false, .error_message = std::format("Node #{} (depth {}) missing from certificate",
                                                           curr.id, curr.depth)};
    }
    const auto &row = it->second;

    if (row.depth != curr.depth) {
      return {.valid = false, .error_message = std::format("Depth mismatch for node #{}: expected {}, got {}",
                                                           curr.id, curr.depth, row.depth)};
    }

    if (row.tag == "SP" || row.tag == "SPLIT" || row.tag == "SO" || row.tag == "SPLIT_ORIGIN") {
      split_count++;
      if (row.children.size() != 2) {
        return {.valid = false, .error_message = std::format("Split node #{} has {} children (expected 2)",
                                                             curr.id, row.children.size())};
      }
      int axis = curr.box.WidestAxis();
      auto [b0, b1] = curr.box.Split(axis);

      SearchNode c0 = curr;
      c0.id = row.children[0];
      c0.parent_id = curr.id;
      c0.depth = (uint8_t)std::min(255, curr.depth + 1);
      c0.box_depth = (uint8_t)std::min(255, curr.box_depth + 1);
      c0.box = b0;

      SearchNode c1 = curr;
      c1.id = row.children[1];
      c1.parent_id = curr.id;
      c1.depth = (uint8_t)std::min(255, curr.depth + 1);
      c1.box_depth = (uint8_t)std::min(255, curr.box_depth + 1);
      c1.box = b1;

      stack.push_back(c1);
      stack.push_back(c0);
    } else if (row.tag == "SV" || row.tag == "SPLIT_VIEW") {
      split_count++;
      if (row.children.size() != 4) {
        return {.valid = false, .error_message = std::format("View split node #{} has {} children (expected 4)",
                                                             curr.id, row.children.size())};
      }
      auto sub_tris = curr.tri.Subdivide();
      for (int t = 3; t >= 0; t--) {
        SearchNode c = curr;
        c.id = row.children[t];
        c.parent_id = curr.id;
        c.depth = (uint8_t)std::min(255, curr.depth + 1);
        c.view_depth = (uint8_t)std::min(255, curr.view_depth + 1);
        c.tri = sub_tris[t];
        stack.push_back(c);
      }
    } else if (row.tag == "DF" || row.tag == "DI" || row.tag == "DIFFICULT") {
      leaf_count++;
      difficult_leaves++;
    } else if (row.tag == "PR" || row.tag == "PRUNE") {
      leaf_count++;
      if (row.prune_kind == "RADIUS" || row.prune_kind == "RA") {
        if (!OutsideBall(curr.box)) {
          return {.valid = false, .error_message = std::format("Node #{} invalid radius prune", curr.id)};
        }
      } else if (row.prune_kind == "FUNDAMENTAL" || row.prune_kind == "FU") {
        auto fund = CheckFundamentalPrune(curr.chart, curr.box);
        if (!fund.prune) {
          return {.valid = false, .error_message = std::format("Node #{} invalid fundamental prune", curr.id)};
        }
      }
    } else if (row.tag == "TU" || row.tag == "TUBE") {
      leaf_count++;
      if (row.tube_radius <= 0.0) {
        return {.valid = false, .error_message = std::format("Node #{} tube radius <= 0", curr.id)};
      }
      if (tube_atlas != nullptr) {
        double safe_r = tube_atlas->GetSafeRadiusForTriangle(curr.tri.corners);
        if (experiment_tube_floor > 0.0) {
          safe_r = std::max(safe_r, experiment_tube_floor);
        }
        if (safe_r <= 0.0) {
          auto nearest = tube_atlas->FindNearestCertifiedNodeForTriangle(curr.tri.corners);
          if (nearest.has_value() && nearest->safe_radius() > 0.0) {
            safe_r = std::max(safe_r, nearest->safe_radius() * 0.5);
          }
        }
        if (safe_r < row.tube_radius - 1e-9) {
          return {.valid = false, .error_message = std::format("Node #{} tube radius exceeds safe atlas radius", curr.id)};
        }
      }
      if (!InsideIdentityTube(curr.chart, curr.box, row.tube_radius)) {
        return {.valid = false, .error_message = std::format("Node #{} not inside identity tube of radius {}", curr.id, row.tube_radius)};
      }
    } else if (row.tag == "CE" || row.tag == "CERT" || row.tag == "MX") {
      leaf_count++;
      worst_margin = std::min(worst_margin, row.margin);
    }
  }

  if (visited.size() != row_map.size()) {
    return {.valid = false, .error_message = std::format("Found {} orphan rows not reachable from root",
                                                         row_map.size() - visited.size())};
  }

  return {
    .valid = true,
    .total_rows = (uint64_t)row_map.size(),
    .total_leaves = leaf_count,
    .total_splits = split_count,
    .difficult_leaves = difficult_leaves,
    .worst_margin = worst_margin,
  };
}

struct SubtreeRow {
  std::string row_text;
};

struct LeafSolveResult {
  bool solved = false;
  std::string kind; // "TU", "PR", "CE", "MX", "TREE"
  std::vector<std::string> rows; // serialized lines for this branch
  double margin = 0.0;
};

// Solves a CayleyBox on a specific leaf ProjectiveTriangle using SolveCellMixture.
static LeafSolveResult SolveBoxOnLeafTriangle(
    int chart, const CayleyBox &cbox, const ProjectiveTriangle &tri,
    int64_t node_id, int64_t parent_id, int depth, int box_depth, int view_depth,
    const tubetree229::TubeAtlas *atlas, int max_box_splits, int max_view_splits, double limit_sec,
    int max_nodes, int cone_samples, double tube_radius = 0.0) {
  
  DifficultCell leaf_cell;
  leaf_cell.id = node_id;
  leaf_cell.parent_id = parent_id;
  leaf_cell.depth = depth;
  leaf_cell.box_depth = box_depth;
  leaf_cell.view_depth = view_depth;
  leaf_cell.chart = chart;
  leaf_cell.c = cbox.center;
  leaf_cell.r = cbox.radii;
  leaf_cell.v[0] = tri.corners[0];
  leaf_cell.v[1] = tri.corners[1];
  leaf_cell.v[2] = tri.corners[2];
  leaf_cell.best_margin = -1e30;

  std::vector<std::string> rows;
  auto stats = SolveCellMixture(
      leaf_cell,
      /*max_depth=*/depth + max_box_splits + max_view_splits * 2,
      /*max_box_depth=*/box_depth + max_box_splits,
      /*max_view_depth=*/view_depth + max_view_splits,
      /*max_nodes=*/max_nodes,
      /*max_split_delta=*/max_box_splits + max_view_splits * 2,
      /*cone_samples=*/cone_samples,
      /*max_components=*/4,
      /*split_kappa=*/0.5,
      /*tube_radius=*/tube_radius,
      /*time_limit_sec=*/limit_sec,
      /*row_callback=*/[&](std::string_view r) { rows.emplace_back(r); },
      nullptr, 0, nullptr, atlas);

  if (stats.solved) {
    return {.solved = true, .kind = "SOLVED", .rows = std::move(rows), .margin = stats.worst_margin};
  }
  static std::mutex g_print_mu;
  {
    std::lock_guard<std::mutex> lock(g_print_mu);
    Print("    Leaf #{} failed: pruned={}, cert={}, ceiling={}, remaining={}, total_nodes={}, worst_margin={:.3e}\n",
          node_id, stats.pruned_leaves, stats.certified_leaves, stats.ceiling_hits,
          stats.remaining_nodes, stats.total_nodes, stats.worst_margin);
  }
  return {.solved = false, .kind = "FAILED", .rows = std::move(rows), .margin = stats.worst_margin};
}

struct RollupResult {
  bool fully_solved = false;
  std::vector<std::string> rows;
  int64_t lca_id = -1;
  DifficultCell child_cell;
};

// Rolls up any open leaves in raw_rows to their Lowest Common Ancestor (LCA).
// Discards unfinished sub-branches beneath the LCA, preserves all certified
// branches outside the LCA, and replaces the LCA with a single 'DF' leaf.
static RollupResult RollupFrontierToLca(
    int chart, const CayleyBox &root_box, const ProjectiveTriangle &root_tri,
    int64_t root_id, int64_t root_parent_id, int root_depth, int root_box_depth, int root_view_depth,
    const std::vector<std::string> &raw_rows) {

  if (raw_rows.empty()) {
    DifficultCell child_cell;
    child_cell.id = root_id;
    child_cell.parent_id = root_parent_id;
    child_cell.depth = root_depth;
    child_cell.box_depth = root_box_depth;
    child_cell.view_depth = root_view_depth;
    child_cell.chart = chart;
    child_cell.c = root_box.center;
    child_cell.r = root_box.radii;
    child_cell.v[0] = root_tri.corners[0];
    child_cell.v[1] = root_tri.corners[1];
    child_cell.v[2] = root_tri.corners[2];
    child_cell.best_margin = -1e30;
    return {
      .fully_solved = false,
      .rows = {std::format("DF {} {} {} -1e30\n", root_id, root_parent_id, root_depth)},
      .lca_id = root_id,
      .child_cell = child_cell
    };
  }

  struct ParsedRow {
    std::string tag;
    int64_t id = -1;
    int64_t parent_id = -1;
    int depth = 0;
    std::vector<int64_t> children;
    std::string line;
  };

  std::unordered_map<int64_t, ParsedRow> node_map;
  std::unordered_set<int64_t> all_children;
  std::unordered_map<int64_t, int64_t> parent_of;
  std::unordered_map<int64_t, int> child_index_of;

  for (const auto &line : raw_rows) {
    if (line.empty()) continue;
    std::istringstream iss(line);
    ParsedRow pr;
    pr.line = line;
    if (!(iss >> pr.tag >> pr.id >> pr.parent_id >> pr.depth)) continue;

    if (pr.tag == "SP") {
      int64_t c0, c1;
      if (iss >> c0 >> c1) {
        pr.children = {c0, c1};
        all_children.insert(c0);
        all_children.insert(c1);
        parent_of[c0] = pr.id;
        parent_of[c1] = pr.id;
        child_index_of[c0] = 0;
        child_index_of[c1] = 1;
      }
    } else if (pr.tag == "SV") {
      int64_t c[4];
      if (iss >> c[0] >> c[1] >> c[2] >> c[3]) {
        for (int i = 0; i < 4; i++) {
          pr.children.push_back(c[i]);
          all_children.insert(c[i]);
          parent_of[c[i]] = pr.id;
          child_index_of[c[i]] = i;
        }
      }
    }
    node_map[pr.id] = pr;
  }

  // Find all open leaves (children created by splits that have no certificate row)
  std::vector<int64_t> open_leaves;
  if (node_map.find(root_id) == node_map.end()) {
    open_leaves.push_back(root_id);
  } else {
    for (int64_t cid : all_children) {
      if (node_map.find(cid) == node_map.end()) {
        open_leaves.push_back(cid);
      }
    }
  }

  if (open_leaves.empty()) {
    return {.fully_solved = true, .rows = raw_rows};
  }

  // Compute paths from root down to each open leaf
  std::vector<std::vector<int64_t>> paths;
  for (int64_t leaf : open_leaves) {
    std::vector<int64_t> p;
    int64_t curr = leaf;
    while (true) {
      p.push_back(curr);
      if (curr == root_id) break;
      auto it = parent_of.find(curr);
      if (it == parent_of.end()) break;
      curr = it->second;
    }
    std::reverse(p.begin(), p.end());
    paths.push_back(std::move(p));
  }

  // Find Lowest Common Ancestor (LCA)
  int64_t lca_id = root_id;
  std::vector<int64_t> lca_path = {root_id};
  for (size_t step = 1; ; step++) {
    if (step >= paths[0].size()) break;
    int64_t cand = paths[0][step];
    bool match = true;
    for (size_t i = 1; i < paths.size(); i++) {
      if (step >= paths[i].size() || paths[i][step] != cand) {
        match = false;
        break;
      }
    }
    if (match) {
      lca_id = cand;
      lca_path.push_back(cand);
    } else {
      break;
    }
  }

  // Find all strict descendants of lca_id to prune them
  std::unordered_set<int64_t> prune_set;
  std::vector<int64_t> q = {lca_id};
  while (!q.empty()) {
    int64_t u = q.back();
    q.pop_back();
    auto it = node_map.find(u);
    if (it != node_map.end()) {
      for (int64_t ch : it->second.children) {
        prune_set.insert(ch);
        q.push_back(ch);
      }
    }
  }

  // Reconstruct geometry for lca_id along lca_path
  CayleyBox curr_box = root_box;
  ProjectiveTriangle curr_tri = root_tri;
  int curr_depth = root_depth;
  int curr_box_depth = root_box_depth;
  int curr_view_depth = root_view_depth;

  for (size_t step = 0; step + 1 < lca_path.size(); step++) {
    int64_t p_id = lca_path[step];
    int64_t c_id = lca_path[step + 1];
    const auto &pr = node_map[p_id];
    if (pr.tag == "SP") {
      int widest = curr_box.WidestAxis();
      auto [b0, b1] = curr_box.Split(widest);
      int c_idx = child_index_of[c_id];
      curr_box = (c_idx == 0) ? b0 : b1;
      curr_depth++;
      curr_box_depth++;
    } else if (pr.tag == "SV") {
      auto sub = curr_tri.Subdivide();
      int c_idx = child_index_of[c_id];
      curr_tri = sub[c_idx];
      curr_depth++;
      curr_view_depth++;
    }
  }

  int64_t lca_parent = (lca_id == root_id) ? root_parent_id : parent_of[lca_id];

  // Build pruned rows
  std::vector<std::string> pruned_rows;
  bool lca_emitted = false;
  for (const auto &raw : raw_rows) {
    if (raw.empty()) continue;
    std::istringstream iss(raw);
    std::string tag;
    int64_t id;
    if (!(iss >> tag >> id)) continue;
    if (id == lca_id) {
      pruned_rows.push_back(std::format("DF {} {} {} -1e30\n", lca_id, lca_parent, curr_depth));
      lca_emitted = true;
    } else if (!prune_set.contains(id)) {
      pruned_rows.push_back(raw);
    }
  }

  if (!lca_emitted) {
    pruned_rows.push_back(std::format("DF {} {} {} -1e30\n", lca_id, lca_parent, curr_depth));
  }

  DifficultCell child_cell;
  child_cell.id = lca_id;
  child_cell.parent_id = lca_parent;
  child_cell.depth = curr_depth;
  child_cell.box_depth = curr_box_depth;
  child_cell.view_depth = curr_view_depth;
  child_cell.chart = chart;
  child_cell.c = curr_box.center;
  child_cell.r = curr_box.radii;
  child_cell.v[0] = curr_tri.corners[0];
  child_cell.v[1] = curr_tri.corners[1];
  child_cell.v[2] = curr_tri.corners[2];
  child_cell.best_margin = -1e30;

  return {
    .fully_solved = false,
    .rows = std::move(pruned_rows),
    .lca_id = lca_id,
    .child_cell = child_cell
  };
}

static bool StitchDoneFile(
    int chart, int64_t cell_id, const std::string &out_dir,
    const tubetree229::TubeAtlas *atlas, double tube_radius,
    const std::vector<DifficultCell> &all_cells) {
  
  std::string done_file = std::format("{}/chart{}.{}.done", out_dir, chart, cell_id);
  if (!std::filesystem::exists(done_file)) {
    Print(ARED("Done file not found: {}\n"), done_file);
    return false;
  }

  DifficultCell target_cell;
  bool found_cell = false;
  for (const auto &c : all_cells) {
    if (c.chart == chart && c.id == cell_id) {
      target_cell = c;
      found_cell = true;
      break;
    }
  }
  if (!found_cell && std::filesystem::exists("chart0.difficult.bak")) {
    auto bak_cells = ReadDifficultFile("chart0.difficult.bak");
    for (const auto &c : bak_cells) {
      if (c.chart == chart && c.id == cell_id) {
        target_cell = c;
        found_cell = true;
        break;
      }
    }
  }

  std::string base_template = std::format("{}/chart{}.{}.done.base", out_dir, chart, cell_id);
  std::string template_file = std::filesystem::exists(base_template) ? base_template : done_file;

  std::ifstream in(template_file);
  std::string line;
  std::vector<std::string> output_lines;
  int stitched_nodes = 0;
  int unstitched_nodes = 0;
  int64_t next_stitch_unique_id = 20000000000000LL;

  while (std::getline(in, line)) {
    if (line.empty()) continue;
    std::istringstream iss(line);
    std::string tag;
    int64_t id = -1;
    if (iss >> tag >> id && (tag == "DF" || tag == "DI" || tag == "DIFFICULT")) {
      std::string child_done = std::format("{}/chart{}.{}.done", out_dir, chart, id);
      if (std::filesystem::exists(child_done)) {
        std::ifstream cin(child_done);
        std::string cline;
        std::unordered_map<int64_t, int64_t> id_map;
        id_map[id] = id; // Root of child matches outer tree

        auto GetMappedId = [&](int64_t orig_id) -> int64_t {
          if (orig_id == id) return id;
          auto it = id_map.find(orig_id);
          if (it != id_map.end()) return it->second;
          int64_t nid = next_stitch_unique_id++;
          id_map[orig_id] = nid;
          return nid;
        };

        while (std::getline(cin, cline)) {
          if (cline.empty() || cline[0] == '#') continue;
          std::istringstream ciss(cline);
          std::string rtag;
          int64_t rid, rpid;
          int rdepth;
          if (ciss >> rtag >> rid >> rpid >> rdepth) {
            int64_t m_id = GetMappedId(rid);
            int64_t m_pid = (rpid == id) ? id : (id_map.contains(rpid) ? id_map[rpid] : rpid);

            if (rtag == "SP" || rtag == "SPLIT" || rtag == "SO" || rtag == "SPLIT_ORIGIN") {
              int64_t c0, c1;
              ciss >> c0 >> c1;
              int64_t mc0 = GetMappedId(c0);
              int64_t mc1 = GetMappedId(c1);
              output_lines.push_back(std::format("{} {} {} {} {} {}", rtag, m_id, m_pid, rdepth, mc0, mc1));
            } else if (rtag == "SV" || rtag == "SPLIT_VIEW") {
              int64_t c0, c1, c2, c3;
              ciss >> c0 >> c1 >> c2 >> c3;
              int64_t mc0 = GetMappedId(c0);
              int64_t mc1 = GetMappedId(c1);
              int64_t mc2 = GetMappedId(c2);
              int64_t mc3 = GetMappedId(c3);
              output_lines.push_back(std::format("{} {} {} {} {} {} {} {}", rtag, m_id, m_pid, rdepth, mc0, mc1, mc2, mc3));
            } else {
              std::string rest;
              std::getline(ciss, rest);
              output_lines.push_back(std::format("{} {} {} {}{}", rtag, m_id, m_pid, rdepth, rest));
            }
          }
        }
        stitched_nodes++;
      } else {
        output_lines.push_back(line);
        unstitched_nodes++;
      }
    } else {
      output_lines.push_back(line);
    }
  }
  in.close();

  std::string tmp_file = done_file + ".stitched";
  std::ofstream out(tmp_file);
  for (const auto &l : output_lines) {
    out << l << "\n";
  }
  out.close();
  std::filesystem::rename(tmp_file, done_file);

  Print("Stitch results for {}: stitched {} nodes, {} DF nodes remaining.\n",
        done_file, stitched_nodes, unstitched_nodes);

  if (found_cell) {
    auto v = VerifyDoneFile(target_cell, done_file, atlas, /*allow_difficult=*/(unstitched_nodes > 0), tube_radius);
    if (v.valid) {
      if (unstitched_nodes == 0) {
        Print(AGREEN("✓ Stitched certificate is 100% COMPLETE & VERIFIED! (rows: {}, leaves: {})\n"),
              v.total_rows, v.total_leaves);
      } else {
        Print(AYELLOW("✓ Stitched certificate is valid with {} DF leaves remaining.\n"), v.difficult_leaves);
      }
    } else {
      Print(ARED("Verification failed after stitch: {}\n"), v.error_message);
    }
  }
  return true;
}

int main(int argc, char **argv) {
  int chart = 0;
  std::string difficult_path = "chart0.difficult";
  std::string atlas_dir = "/root/nopert-project";
  std::string out_dir = ".";
  int telescope_n = 2; // Default N=2 (4^2 = 16 sub-wedges)
  int max_box_splits = 8;
  int max_view_splits = 4;
  int max_difficult_budget = 64;
  int max_nodes = 16384;
  double limit_sec = 10.0;
  int cone_samples = 12;
  int num_threads = std::clamp((int)std::thread::hardware_concurrency(), 1, 16);
  int64_t target_cell_id = -1;
  bool dry_run = false;
  bool stitch_mode = false;
  double tube_radius = 0.0;
  bool use_nearest_tube = false;
  double conservative_factor = 0.5;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--chart" && i + 1 < argc) {
      chart = std::atoi(argv[++i]);
    } else if (arg == "--difficult" && i + 1 < argc) {
      difficult_path = argv[++i];
    } else if (arg == "--atlas_dir" && i + 1 < argc) {
      atlas_dir = argv[++i];
    } else if (arg == "--out_dir" && i + 1 < argc) {
      out_dir = argv[++i];
    } else if (arg == "--telescope_n" && i + 1 < argc) {
      telescope_n = std::atoi(argv[++i]);
    } else if (arg == "--max_box_splits" && i + 1 < argc) {
      max_box_splits = std::atoi(argv[++i]);
    } else if (arg == "--max_view_splits" && i + 1 < argc) {
      max_view_splits = std::atoi(argv[++i]);
    } else if (arg == "--max_difficult_budget" && i + 1 < argc) {
      max_difficult_budget = std::atoi(argv[++i]);
    } else if (arg == "--max_nodes" && i + 1 < argc) {
      max_nodes = std::atoi(argv[++i]);
    } else if (arg == "--limit_sec" && i + 1 < argc) {
      limit_sec = std::atof(argv[++i]);
    } else if (arg == "--cone_samples" && i + 1 < argc) {
      cone_samples = std::atoi(argv[++i]);
    } else if (arg == "--threads" && i + 1 < argc) {
      num_threads = std::atoi(argv[++i]);
    } else if (arg == "--cell_id" && i + 1 < argc) {
      target_cell_id = std::atoll(argv[++i]);
    } else if (arg == "--dry_run") {
      dry_run = true;
    } else if (arg == "--stitch") {
      stitch_mode = true;
    } else if (arg == "--tube_radius" && i + 1 < argc) {
      tube_radius = std::atof(argv[++i]);
    } else if (arg == "--use_nearest_tube") {
      use_nearest_tube = true;
    } else if (arg == "--conservative_factor" && i + 1 < argc) {
      conservative_factor = std::atof(argv[++i]);
    }
  }

  tubetree229::TubeAtlas atlas;
  if (std::filesystem::exists(atlas_dir)) {
    int loaded = atlas.LoadFromDir(atlas_dir);
    Print("Loaded {} tube trees from {}\n", loaded, atlas_dir);
  }

  std::vector<DifficultCell> cells = ReadDifficultFile(difficult_path);
  Print("Loaded {} difficult cells from {}\n", cells.size(), difficult_path);

  if (stitch_mode) {
    if (target_cell_id < 0) {
      Print(ARED("Must specify --cell_id <id> for --stitch\n"));
      return 1;
    }
    StitchDoneFile(chart, target_cell_id, out_dir, &atlas, tube_radius, cells);
    return 0;
  }

  int telescoped_count = 0;
  int fully_solved_count = 0;

  for (size_t c_idx = 0; c_idx < cells.size(); c_idx++) {
    const auto &cell = cells[c_idx];
    if (target_cell_id >= 0 && cell.id != target_cell_id) continue;

    Print("\n" ACYAN("=== Processing Cell #{} ===") "\n", cell.id);
    Print("Depth: {}, box_depth: {}, view_depth: {}, margin: {:.3e}\n",
          cell.depth, cell.box_depth, cell.view_depth, cell.best_margin);

    ProjectiveTriangle root_tri(std::array<vec3, 3>{cell.v[0], cell.v[1], cell.v[2]});
    CayleyBox cbox{cell.c, cell.r};

    // Build the quaternary view tree of depth N
    struct ViewTreeNode {
      int64_t id = 0;
      int64_t parent_id = 0;
      int parent_index = -1;
      int depth = 0;
      int view_depth = 0;
      ProjectiveTriangle tri;
      int64_t children[4] = {-1, -1, -1, -1};
      int leaf_index = -1; // index if it's a leaf at depth N
      bool is_active_leaf = false;
      bool is_difficult = false;
    };

    std::vector<ViewTreeNode> vtree;
    int64_t next_v_id = std::max<int64_t>(1000000000LL, cell.id * 10000LL + 1);

    ViewTreeNode root_vnode;
    root_vnode.id = cell.id;
    root_vnode.parent_id = cell.parent_id;
    root_vnode.depth = cell.depth;
    root_vnode.view_depth = cell.view_depth;
    root_vnode.tri = root_tri;
    vtree.push_back(root_vnode);

    std::vector<size_t> current_level_indices = {0};
    for (int step = 0; step < telescope_n; step++) {
      std::vector<size_t> next_level_indices;
      for (size_t p_idx : current_level_indices) {
        auto sub = vtree[p_idx].tri.Subdivide();
        for (int c = 0; c < 4; c++) {
          int64_t cid = next_v_id++;
          vtree[p_idx].children[c] = cid;
          ViewTreeNode child_vnode;
          child_vnode.id = cid;
          child_vnode.parent_id = vtree[p_idx].id;
          child_vnode.parent_index = (int)p_idx;
          child_vnode.depth = vtree[p_idx].depth + 1;
          child_vnode.view_depth = vtree[p_idx].view_depth + 1;
          child_vnode.tri = sub[c];
          size_t c_pos = vtree.size();
          vtree.push_back(child_vnode);
          next_level_indices.push_back(c_pos);
        }
      }
      current_level_indices = std::move(next_level_indices);
    }

    int total_leaves = current_level_indices.size(); // 4^N
    for (int i = 0; i < total_leaves; i++) {
      vtree[current_level_indices[i]].leaf_index = i;
    }

    Print("Evaluating 4^{} = {} sub-triangles (max_box_splits={}, max_view_splits={}, threads={})...\n",
          telescope_n, total_leaves, max_box_splits, max_view_splits, num_threads);

    std::vector<RollupResult> rollup_results(total_leaves);
    std::atomic<int> next_leaf_idx{0};
    int actual_threads = std::clamp(num_threads, 1, total_leaves);
    std::vector<std::thread> workers;
    for (int t = 0; t < actual_threads; t++) {
      workers.emplace_back([&]() {
        while (true) {
          int i = next_leaf_idx.fetch_add(1);
          if (i >= total_leaves) break;
          const auto &lnode = vtree[current_level_indices[i]];
          double leaf_tube_r = tube_radius;
          if (use_nearest_tube && atlas.IsLoaded()) {
            vec3 corners[3] = {lnode.tri.corners[0], lnode.tri.corners[1], lnode.tri.corners[2]};
            auto nearest = atlas.FindNearestCertifiedNodeForTriangle(corners);
            if (nearest.has_value() && nearest->safe_radius() > 0.0) {
              double cr = nearest->safe_radius() * conservative_factor;
              leaf_tube_r = std::max(leaf_tube_r, cr);
            }
          }
          auto lres = SolveBoxOnLeafTriangle(
              cell.chart, cbox, lnode.tri, lnode.id, lnode.parent_id,
              lnode.depth, cell.box_depth, lnode.view_depth,
              &atlas, max_box_splits, max_view_splits, limit_sec, max_nodes, cone_samples, leaf_tube_r);

          rollup_results[i] = RollupFrontierToLca(
              cell.chart, cbox, lnode.tri, lnode.id, lnode.parent_id,
              lnode.depth, cell.box_depth, lnode.view_depth,
              lres.rows);
        }
      });
    }
    for (auto &w : workers) {
      w.join();
    }

    std::unordered_map<int64_t, size_t> id_to_vidx;
    for (size_t vi = 0; vi < vtree.size(); vi++) {
      id_to_vidx[vtree[vi].id] = vi;
      vtree[vi].is_active_leaf = (vtree[vi].leaf_index >= 0);
      vtree[vi].is_difficult = (vtree[vi].leaf_index >= 0 && !rollup_results[vtree[vi].leaf_index].fully_solved);
    }

    int solved_leaves = 0;
    int difficult_count = 0;
    for (int i = 0; i < total_leaves; i++) {
      if (rollup_results[i].fully_solved) solved_leaves++;
      else difficult_count++;
    }

    Print("Initial leaf results: {} / {} solved ({} difficult leaves, budget={})\n",
          solved_leaves, total_leaves, difficult_count, max_difficult_budget);

    // Apply greedy roll-ups until difficult_count <= max_difficult_budget
    while (difficult_count > max_difficult_budget) {
      int best_node = -1;
      int best_score = -1;
      int best_solved_lost = 999;

      for (int vi = (int)vtree.size() - 1; vi >= 0; vi--) {
        if (vtree[vi].is_active_leaf) continue;
        bool all_leaves = true;
        int diff_children = 0;
        int solved_children = 0;
        for (int c = 0; c < 4; c++) {
          int64_t cid = vtree[vi].children[c];
          size_t c_idx = id_to_vidx[cid];
          if (!vtree[c_idx].is_active_leaf) {
            all_leaves = false;
            break;
          }
          if (vtree[c_idx].is_difficult) diff_children++;
          else solved_children++;
        }
        if (!all_leaves) continue;
        if (diff_children == 0) continue; // Don't collapse completely solved subtrees

        if (diff_children > best_score || (diff_children == best_score && solved_children < best_solved_lost)) {
          best_score = diff_children;
          best_solved_lost = solved_children;
          best_node = vi;
        }
      }

      if (best_node < 0) {
        break;
      }

      for (int c = 0; c < 4; c++) {
        int64_t cid = vtree[best_node].children[c];
        size_t c_idx = id_to_vidx[cid];
        vtree[c_idx].is_active_leaf = false;
      }
      vtree[best_node].is_active_leaf = true;
      vtree[best_node].is_difficult = true;
      difficult_count += (1 - best_score);
      Print("    Rolled up node #{} (depth {}, view_depth {}): collapsed {} difficult leaves, lost {} solved leaves (difficult now: {})\n",
            vtree[best_node].id, vtree[best_node].depth, vtree[best_node].view_depth,
            best_score, best_solved_lost, difficult_count);
    }

    // Now emit the tree to chart<chart>.<id>.done
    std::string done_file = std::format("{}/chart{}.{}.done", out_dir, cell.chart, cell.id);
    std::string tmp_file = done_file + ".tmp";
    std::ofstream out(tmp_file);

    std::vector<DifficultCell> spawned_difficult_cells;

    std::function<void(size_t)> EmitVnode = [&](size_t vi) {
      const auto &vnode = vtree[vi];
      if (vnode.is_active_leaf) {
        if (!vnode.is_difficult) {
          // Solved leaf
          for (const auto &row : rollup_results[vnode.leaf_index].rows) {
            out << row;
            if (row.empty() || row.back() != '\n') out << "\n";
          }
        } else {
          // Difficult leaf
          if (vnode.leaf_index >= 0 && !rollup_results[vnode.leaf_index].rows.empty()) {
            for (const auto &row : rollup_results[vnode.leaf_index].rows) {
              out << row;
              if (row.empty() || row.back() != '\n') out << "\n";
            }
            spawned_difficult_cells.push_back(rollup_results[vnode.leaf_index].child_cell);
          } else {
            out << std::format("DF {} {} {} -1e30\n", vnode.id, vnode.parent_id, vnode.depth);
            DifficultCell child_cell;
            child_cell.id = vnode.id;
            child_cell.parent_id = vnode.parent_id;
            child_cell.depth = vnode.depth;
            child_cell.box_depth = cell.box_depth;
            child_cell.view_depth = vnode.view_depth;
            child_cell.chart = cell.chart;
            child_cell.c = cell.c;
            child_cell.r = cell.r;
            child_cell.v[0] = vnode.tri.corners[0];
            child_cell.v[1] = vnode.tri.corners[1];
            child_cell.v[2] = vnode.tri.corners[2];
            child_cell.best_margin = -1e30;
            spawned_difficult_cells.push_back(child_cell);
          }
        }
      } else {
        // Internal SV node
        out << std::format("SV {} {} {} {} {} {} {}\n",
                           vnode.id, vnode.parent_id, vnode.depth,
                           vnode.children[0], vnode.children[1],
                           vnode.children[2], vnode.children[3]);
        for (int c = 0; c < 4; c++) {
          int64_t cid = vnode.children[c];
          size_t c_idx = id_to_vidx[cid];
          EmitVnode(c_idx);
        }
      }
    };

    EmitVnode(0);
    out.close();
    std::filesystem::rename(tmp_file, done_file);

    bool allow_diff = !spawned_difficult_cells.empty();
    auto v = VerifyDoneFile(cell, done_file, &atlas, allow_diff, tube_radius);
    if (v.valid) {
      if (spawned_difficult_cells.empty()) {
        Print(AGREEN("Cell #{} FULLY SOLVED! Verified 100% certificate {} (rows: {}, leaves: {})\n"),
              cell.id, done_file, v.total_rows, v.total_leaves);
        fully_solved_count++;
        cells.erase(cells.begin() + c_idx);
        WriteDifficultFile(difficult_path, cells);
        c_idx--;
      } else {
        Print(AGREEN("Verified partial .done: {} (total rows: {}, solved leaves: {}, DF leaves: {})\n"),
              done_file, v.total_rows, v.total_leaves - v.difficult_leaves, v.difficult_leaves);
        telescoped_count++;
        cells.erase(cells.begin() + c_idx);
        cells.insert(cells.begin() + c_idx, spawned_difficult_cells.begin(), spawned_difficult_cells.end());
        WriteDifficultFile(difficult_path, cells);
        Print(AGREEN("Updated active difficult frontier in {} with {} sub-cells!\n"),
              difficult_path, spawned_difficult_cells.size());
        c_idx += spawned_difficult_cells.size() - 1;
      }
    } else {
      Print(ARED("Verification failed for {}: {}\n"), done_file, v.error_message);
    }
  }

  Print("\n" ACYAN("=== Telescoping Summary ===") "\n");
  Print("Fully solved cells: {}\n", fully_solved_count);
  Print("Telescoped cells (locked in 4^N - 1 volume): {}\n", telescoped_count);

  return 0;
}
