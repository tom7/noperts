#ifndef _RUPERTS_FLATTEN_CHARTS_H
#define _RUPERTS_FLATTEN_CHARTS_H

#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

#include "chart229.h"
#include "lib229.h"

namespace flatten_charts {

struct FlattenOptions {
  int threshold = 50000;
  std::string subcharts_dir = "/mnt/nopertdata";
  bool dry_run = false;
  bool keep_subcharts = false;
  bool verbose = false;
};

struct FlattenStats {
  int df_rows_found = 0;
  int files_absorbed = 0;
  int64_t rows_absorbed = 0;
  int files_converted_to_subchart = 0;
  int subcharts_removed = 0;
  int unresolved_df = 0;
  int pending_df = 0;
  int geometry_errors = 0;
};

struct NodeGeometry {
  int64_t id = 0;
  int64_t parent_id = -1;
  int depth = 0;
  int box_depth = 0;
  int view_depth = 0;
  int chart = 0;
  CayleyBox box;
  ProjectiveTriangle tri;
};

inline NodeGeometry DefaultRootGeometry(int chart) {
  NodeGeometry root;
  root.id = 0;
  root.parent_id = -1;
  root.depth = 0;
  root.box_depth = 0;
  root.view_depth = 0;
  root.chart = chart;
  root.box.center = {0.0, 0.0, 0.0};
  if (chart == 0) {
    root.box.radii = {1.0, 1.0, 1.0 / 3.0};
  } else if (chart == 1) {
    root.box.radii = {1.0, 1.0 / 3.0, 1.0};
  } else if (chart == 2) {
    root.box.radii = {1.0 / 3.0, 1.0, 1.0};
  } else {
    root.box.radii = {1.0, 1.0, 1.0};
  }
  root.tri.corners[0] = {1.0, 0.0, 0.0};
  root.tri.corners[1] = {10.0 / 41.0, 31.0 / 41.0, 0.0};
  root.tri.corners[2] = {0.0, 0.0, 1.0};
  return root;
}

inline NodeGeometry FromGeometryRow(const Chart229::GeometryRow &ge) {
  NodeGeometry node;
  node.id = ge.id;
  node.parent_id = ge.parent_id;
  node.depth = ge.depth;
  node.box_depth = ge.box_depth;
  node.view_depth = ge.view_depth;
  node.chart = ge.chart;
  node.box.center = {ge.cx, ge.cy, ge.cz};
  node.box.radii = {ge.rx, ge.ry, ge.rz};
  node.tri.corners[0] = {ge.v0x, ge.v0y, ge.v0z};
  node.tri.corners[1] = {ge.v1x, ge.v1y, ge.v1z};
  node.tri.corners[2] = {ge.v2x, ge.v2y, ge.v2z};
  return node;
}

inline Chart229::GeometryRow MakeGeometryRow(const NodeGeometry &geom) {
  return Chart229::GeometryRow{
      .id = geom.id,
      .parent_id = geom.parent_id,
      .depth = geom.depth,
      .box_depth = geom.box_depth,
      .view_depth = geom.view_depth,
      .chart = geom.chart,
      .cx = geom.box.center.x,
      .cy = geom.box.center.y,
      .cz = geom.box.center.z,
      .rx = geom.box.radii.x,
      .ry = geom.box.radii.y,
      .rz = geom.box.radii.z,
      .v0x = geom.tri.corners[0].x,
      .v0y = geom.tri.corners[0].y,
      .v0z = geom.tri.corners[0].z,
      .v1x = geom.tri.corners[1].x,
      .v1y = geom.tri.corners[1].y,
      .v1z = geom.tri.corners[1].z,
      .v2x = geom.tri.corners[2].x,
      .v2y = geom.tri.corners[2].y,
      .v2z = geom.tri.corners[2].z,
      .best_margin = 0.0,
  };
}

enum class SplitType : uint8_t {
  BOX,
  VIEW
};

struct SplitRecord {
  int64_t parent_id = -1;
  SplitType type = SplitType::BOX;
  std::vector<int64_t> children;
};

inline std::optional<NodeGeometry> TraceGeometry(
    int64_t target_id,
    int64_t parent_id,
    const NodeGeometry &root_geom,
    const std::unordered_map<int64_t, SplitRecord> &splits,
    const std::unordered_map<int64_t, int64_t> *parent_of = nullptr) {
  if (target_id == root_geom.id) {
    return root_geom;
  }

  struct Step {
    int64_t split_id;
    int child_idx;
  };
  std::vector<Step> path;

  int64_t curr_child = target_id;
  int64_t curr_parent = parent_id;

  while (true) {
    auto it = splits.find(curr_parent);
    if (it == splits.end()) {
      if (curr_parent == root_geom.id) {
        break;
      }
      return std::nullopt;
    }
    const auto &rec = it->second;
    int child_idx = -1;
    for (size_t c = 0; c < rec.children.size(); c++) {
      if (rec.children[c] == curr_child) {
        child_idx = static_cast<int>(c);
        break;
      }
    }
    if (child_idx == -1 && parent_of != nullptr) {
      if (rec.type == SplitType::BOX) {
        auto it_prev = parent_of->find(curr_child - 1);
        if (it_prev != parent_of->end() && it_prev->second == curr_parent) {
          child_idx = 1;
        } else {
          auto it_next = parent_of->find(curr_child + 1);
          if (it_next != parent_of->end() && it_next->second == curr_parent) {
            child_idx = 0;
          }
        }
      } else if (rec.type == SplitType::VIEW) {
        for (int k = 0; k < 4; k++) {
          int64_t base = curr_child - k;
          bool all_match = true;
          for (int j = 0; j < 4; j++) {
            auto pj = parent_of->find(base + j);
            if (pj == parent_of->end() || pj->second != curr_parent) {
              all_match = false;
              break;
            }
          }
          if (all_match) {
            child_idx = k;
            break;
          }
        }
      }
    }
    if (child_idx == -1) {
      return std::nullopt;
    }

    path.push_back(Step{.split_id = curr_parent, .child_idx = child_idx});
    if (curr_parent == root_geom.id) {
      break;
    }
    curr_child = curr_parent;
    curr_parent = rec.parent_id;
  }

  NodeGeometry geom = root_geom;
  for (auto it = path.rbegin(); it != path.rend(); ++it) {
    auto it_split = splits.find(it->split_id);
    if (it_split == splits.end()) return std::nullopt;
    const auto &rec = it_split->second;
    if (rec.type == SplitType::BOX) {
      int axis = geom.box.WidestAxis();
      auto [b0, b1] = geom.box.Split(axis);
      int branch = it->child_idx % 2;
      geom.box = (branch == 0) ? b0 : b1;
      geom.box_depth++;
      geom.depth++;
      geom.parent_id = it->split_id;
      geom.id = (static_cast<size_t>(branch) < rec.children.size()) ? rec.children[branch] : it->split_id;
    } else {
      auto sub_tris = geom.tri.Subdivide();
      int branch = it->child_idx % 4;
      geom.tri = sub_tris[branch];
      geom.view_depth++;
      geom.depth++;
      geom.parent_id = it->split_id;
      geom.id = (static_cast<size_t>(branch) < rec.children.size()) ? rec.children[branch] : it->split_id;
    }
  }

  return geom;
}

inline std::string FindExternalFile(const std::string &subcharts_dir, int chart, int64_t id) {
  std::string hex_id = std::format("{:x}", id);
  std::string path = std::format("{}/chart{}.{}.subchart", subcharts_dir, chart, hex_id);
  if (std::filesystem::exists(path)) {
    return path;
  }
  return "";
}

// Result of processing an external file
struct ProcessExternalResult {
  bool absorbed = false;
  std::vector<std::string> replacement_lines;
};

// Recursively processes an external subchart file (absorbing <= threshold).
inline ProcessExternalResult ProcessExternalFile(
    const std::string &ext_path,
    const NodeGeometry &node_geom,
    const FlattenOptions &options,
    int64_t &next_avail_id,
    FlattenStats &stats,
    int recursion_depth = 0) {
  ProcessExternalResult result;

  std::ifstream f(ext_path);
  if (!f.is_open()) {
    std::cerr << "Warning: Cannot open external subchart file: " << ext_path << "\n";
    stats.unresolved_df++;
    return result;
  }

  std::vector<std::string> lines;
  std::string line;
  int row_count = 0;
  bool had_ge_header = false;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    if (line.rfind("ge ", 0) == 0 || line.rfind("GE ", 0) == 0) {
      had_ge_header = true;
      continue;
    }
    lines.push_back(line);
    row_count++;
  }
  f.close();

  if (lines.empty()) {
    std::cerr << "Warning: Empty external subchart file: " << ext_path << "\n";
    stats.unresolved_df++;
    return result;
  }

  // Check threshold
  if (row_count > options.threshold) {
    // Large file: leave split as standalone subchart!
    if (!had_ge_header && !options.dry_run) {
      // Ensure geometry header is prepended
      std::string tmp_path = ext_path + ".tmp";
      std::ofstream out(tmp_path);
      if (out.is_open()) {
        Chart229::GeometryRow ge_row = MakeGeometryRow(node_geom);
        out << Chart229::Serialize(ge_row) << "\n";
        for (const auto &l : lines) {
          out << l << "\n";
        }
        out.close();
        std::filesystem::rename(tmp_path, ext_path);
      }
    }

    // Since it's large, we do not absorb it into the parent; parent keeps df row.
    result.absorbed = false;
    return result;
  }

  // Small file (<= threshold): absorb into parent!
  if (options.verbose) {
    std::cout << "Absorbing " << ext_path << " (" << row_count
              << " rows <= " << options.threshold << ") into parent at depth "
              << node_geom.depth << "\n";
  }

  // Parse rows of external file
  std::vector<Chart229::Row> parsed_rows;
  parsed_rows.reserve(lines.size());
  for (const auto &l : lines) {
    parsed_rows.push_back(Chart229::Parse(l));
  }

  // Find root ID in external file
  int64_t ext_root_id = -1;
  for (const auto &row : parsed_rows) {
    std::visit([&](const auto &r) {
      if constexpr (requires { r.id; }) {
        if (ext_root_id == -1) {
          ext_root_id = r.id;
        }
      }
    }, row);
    if (ext_root_id != -1) break;
  }

  if (ext_root_id == -1) {
    std::cerr << "Error: No valid root row found in " << ext_path << "\n";
    stats.unresolved_df++;
    return result;
  }

  // ID remapping: boundary root maps to parent's node_geom.id; descendants get fresh IDs.
  std::unordered_map<int64_t, int64_t> id_map;
  id_map[ext_root_id] = node_geom.id;

  auto get_mapped_id = [&](int64_t raw_id) -> int64_t {
    if (raw_id < 0) return raw_id;
    auto it = id_map.find(raw_id);
    if (it != id_map.end()) return it->second;
    int64_t nid = ++next_avail_id;
    id_map[raw_id] = nid;
    return nid;
  };

  // Build splits inside this absorbed subtree for geometry propagation in case of nested df rows
  std::unordered_map<int64_t, SplitRecord> sub_splits;
  for (const auto &row : parsed_rows) {
    std::visit([&](const auto &r) {
      using T = std::decay_t<decltype(r)>;
      if constexpr (std::is_same_v<T, Chart229::SplitRow> ||
                    std::is_same_v<T, Chart229::SplitOriginRow>) {
        sub_splits[r.id] = SplitRecord{
            .parent_id = r.parent_id,
            .type = SplitType::BOX,
            .children = {r.child0, r.child1},
        };
      } else if constexpr (std::is_same_v<T, Chart229::SplitViewRow>) {
        sub_splits[r.id] = SplitRecord{
            .parent_id = r.parent_id,
            .type = SplitType::VIEW,
            .children = {r.child0, r.child1, r.child2, r.child3},
        };
      }
    }, row);
  }

  NodeGeometry sub_root_geom = node_geom;
  sub_root_geom.id = ext_root_id;

  // Process rows, remapping IDs and handling any nested df rows recursively
  for (const auto &row : parsed_rows) {
    std::string serialized;
    bool handled_nested = false;

    std::visit([&](const auto &r) {
      using T = std::decay_t<decltype(r)>;
      if constexpr (std::is_same_v<T, Chart229::DifficultRow>) {
        // Nested df row!
        stats.df_rows_found++;
        int64_t nested_raw_id = r.id;
        int64_t nested_raw_parent = r.parent_id;

        auto nested_geom_opt = TraceGeometry(nested_raw_id, nested_raw_parent, sub_root_geom, sub_splits);
        if (nested_geom_opt.has_value()) {
          NodeGeometry nested_geom = *nested_geom_opt;
          nested_geom.id = get_mapped_id(nested_raw_id);
          nested_geom.parent_id = get_mapped_id(nested_raw_parent);

          std::string nested_file = FindExternalFile(options.subcharts_dir, node_geom.chart, nested_raw_id);
          if (!nested_file.empty()) {
            auto nested_res = ProcessExternalFile(
                nested_file, nested_geom, options, next_avail_id, stats, recursion_depth + 1);
            if (nested_res.absorbed) {
              for (const auto &nl : nested_res.replacement_lines) {
                result.replacement_lines.push_back(nl);
              }
              handled_nested = true;
              return;
            }
          } else {
            stats.unresolved_df++;
          }
        }

        // Not absorbed: emit df with mapped IDs
        Chart229::DifficultRow mapped_df = r;
        mapped_df.id = get_mapped_id(r.id);
        mapped_df.parent_id = get_mapped_id(r.parent_id);
        serialized = Chart229::Serialize(mapped_df);
      } else if constexpr (std::is_same_v<T, Chart229::SplitRow>) {
        Chart229::SplitRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        m.child0 = get_mapped_id(r.child0);
        m.child1 = get_mapped_id(r.child1);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::SplitOriginRow>) {
        Chart229::SplitOriginRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        m.child0 = get_mapped_id(r.child0);
        m.child1 = get_mapped_id(r.child1);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::SplitViewRow>) {
        Chart229::SplitViewRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        m.child0 = get_mapped_id(r.child0);
        m.child1 = get_mapped_id(r.child1);
        m.child2 = get_mapped_id(r.child2);
        m.child3 = get_mapped_id(r.child3);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::CertRow>) {
        Chart229::CertRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::MixedCertRow>) {
        Chart229::MixedCertRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::PruneRadiusRow>) {
        Chart229::PruneRadiusRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::PruneFundamentalRow>) {
        Chart229::PruneFundamentalRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::TubeRow>) {
        Chart229::TubeRow m = r;
        m.id = get_mapped_id(r.id);
        m.parent_id = get_mapped_id(r.parent_id);
        serialized = Chart229::Serialize(m);
      } else if constexpr (std::is_same_v<T, Chart229::CommentRow>) {
        serialized = Chart229::Serialize(r);
      } else if constexpr (std::is_same_v<T, Chart229::EmptyRow>) {
        serialized = "";
      } else {
        // Fallback for any other row
        serialized = Chart229::Serialize(r);
      }
    }, row);

    if (!handled_nested && !serialized.empty()) {
      result.replacement_lines.push_back(serialized);
    }
  }

  // Remove the absorbed file if not keeping subchart files
  if (!options.dry_run && !options.keep_subcharts) {
    std::error_code ec;
    std::filesystem::remove(ext_path, ec);
    if (!ec) {
      stats.subcharts_removed++;
    }
  }

  stats.files_absorbed++;
  stats.rows_absorbed += result.replacement_lines.size();
  result.absorbed = true;
  return result;
}

// Flattens a single chart or subchart file.
inline bool FlattenChartFile(
    const std::string &in_path,
    const std::string &out_path,
    const FlattenOptions &options,
    FlattenStats &stats,
    int default_chart = 0) {

  std::ifstream infile(in_path);
  if (!infile.is_open()) {
    std::cerr << "Error: Cannot open " << in_path << "\n";
    return false;
  }

  // Infer chart number from filename if possible
  int chart_num = default_chart;
  std::string filename = std::filesystem::path(in_path).filename().string();
  if (filename.rfind("chart0", 0) == 0) chart_num = 0;
  else if (filename.rfind("chart1", 0) == 0) chart_num = 1;
  else if (filename.rfind("chart2", 0) == 0) chart_num = 2;

  // Pass 1: Scan file, parse ge header if present, record splits and df rows, find max_id
  std::optional<Chart229::GeometryRow> ge_header;
  std::unordered_map<int64_t, SplitRecord> splits;
  std::unordered_map<int64_t, int64_t> parent_of;
  struct DfOccurrence {
    int64_t id;
    int64_t parent_id;
    int depth;
  };
  std::vector<DfOccurrence> df_nodes;
  std::unordered_set<int64_t> df_ids;
  int64_t max_id = 0;

  std::string line;
  bool is_first_line = true;
  while (std::getline(infile, line)) {
    if (line.empty() || line[0] == '#') continue;

    if (is_first_line) {
      is_first_line = false;
      if (line.rfind("ge ", 0) == 0 || line.rfind("GE ", 0) == 0) {
        Chart229::Row r = Chart229::Parse(line);
        if (std::holds_alternative<Chart229::GeometryRow>(r)) {
          ge_header = std::get<Chart229::GeometryRow>(r);
          chart_num = ge_header->chart;
          max_id = std::max(max_id, ge_header->id);
          continue;
        }
      }
    }

    if (line.rfind("df ", 0) == 0 || line.rfind("DF ", 0) == 0 ||
        line.rfind("di ", 0) == 0 || line.rfind("DI ", 0) == 0) {
      Chart229::Row r = Chart229::Parse(line);
      if (std::holds_alternative<Chart229::DifficultRow>(r)) {
        const auto &df = std::get<Chart229::DifficultRow>(r);
        df_nodes.push_back(DfOccurrence{
            .id = df.id,
            .parent_id = df.parent_id,
            .depth = df.depth,
        });
        df_ids.insert(df.id);
        parent_of[df.id] = df.parent_id;
        max_id = std::max(max_id, df.id);
      }
      continue;
    }

    if (line.rfind("sp ", 0) == 0 || line.rfind("SP ", 0) == 0 ||
        line.rfind("so ", 0) == 0 || line.rfind("SO ", 0) == 0) {
      Chart229::Row r = Chart229::Parse(line);
      if (std::holds_alternative<Chart229::SplitRow>(r)) {
        const auto &sp = std::get<Chart229::SplitRow>(r);
        parent_of[sp.id] = sp.parent_id;
        parent_of[sp.child0] = sp.id;
        parent_of[sp.child1] = sp.id;
        auto [it, inserted] = splits.try_emplace(sp.id, SplitRecord{
            .parent_id = sp.parent_id,
            .type = SplitType::BOX,
            .children = {sp.child0, sp.child1},
        });
        if (!inserted) {
          it->second.children.push_back(sp.child0);
          it->second.children.push_back(sp.child1);
        }
        max_id = std::max({max_id, sp.id, sp.child0, sp.child1});
      } else if (std::holds_alternative<Chart229::SplitOriginRow>(r)) {
        const auto &so = std::get<Chart229::SplitOriginRow>(r);
        parent_of[so.id] = so.parent_id;
        parent_of[so.child0] = so.id;
        parent_of[so.child1] = so.id;
        auto [it, inserted] = splits.try_emplace(so.id, SplitRecord{
            .parent_id = so.parent_id,
            .type = SplitType::BOX,
            .children = {so.child0, so.child1},
        });
        if (!inserted) {
          it->second.children.push_back(so.child0);
          it->second.children.push_back(so.child1);
        }
        max_id = std::max({max_id, so.id, so.child0, so.child1});
      }
      continue;
    }

    if (line.rfind("sv ", 0) == 0 || line.rfind("SV ", 0) == 0) {
      Chart229::Row r = Chart229::Parse(line);
      if (std::holds_alternative<Chart229::SplitViewRow>(r)) {
        const auto &sv = std::get<Chart229::SplitViewRow>(r);
        parent_of[sv.id] = sv.parent_id;
        parent_of[sv.child0] = sv.id;
        parent_of[sv.child1] = sv.id;
        parent_of[sv.child2] = sv.id;
        parent_of[sv.child3] = sv.id;
        auto [it, inserted] = splits.try_emplace(sv.id, SplitRecord{
            .parent_id = sv.parent_id,
            .type = SplitType::VIEW,
            .children = {sv.child0, sv.child1, sv.child2, sv.child3},
        });
        if (!inserted) {
          it->second.children.push_back(sv.child0);
          it->second.children.push_back(sv.child1);
          it->second.children.push_back(sv.child2);
          it->second.children.push_back(sv.child3);
        }
        max_id = std::max({max_id, sv.id, sv.child0, sv.child1, sv.child2, sv.child3});
      }
      continue;
    }

    // For other rows, extract ID to track max_id and parent
    Chart229::Row r = Chart229::Parse(line);
    std::visit([&](const auto &row_val) {
      if constexpr (requires { row_val.id; }) {
        max_id = std::max(max_id, row_val.id);
        if constexpr (requires { row_val.parent_id; }) {
          parent_of[row_val.id] = row_val.parent_id;
        }
      }
    }, r);
  }
  infile.close();

  stats.df_rows_found += df_nodes.size();

  if (df_nodes.empty()) {
    if (options.verbose) {
      std::cout << in_path << ": No df rows found; chart is already completely flat.\n";
    }
    return true;
  }

  // Initialize root geometry
  NodeGeometry root_geom;
  if (ge_header.has_value()) {
    root_geom = FromGeometryRow(*ge_header);
  } else {
    root_geom = DefaultRootGeometry(chart_num);
  }

  // Next available ID for freshly remapped descendant nodes
  int64_t next_avail_id = max_id;

  // Process all df nodes to prepare replacements or conversions
  std::unordered_map<int64_t, std::vector<std::string>> replacements;

  for (const auto &df : df_nodes) {
    auto geom_opt = TraceGeometry(df.id, df.parent_id, root_geom, splits, &parent_of);
    if (!geom_opt.has_value()) {
      std::cerr << "Warning: Could not trace geometry for df node "
                << std::format("{:x}", df.id) << " (parent "
                << std::format("{:x}", df.parent_id) << ") in " << in_path << "\n";
      stats.geometry_errors++;
      continue;
    }

    NodeGeometry geom = *geom_opt;
    std::string ext_file = FindExternalFile(options.subcharts_dir, chart_num, df.id);
    if (ext_file.empty()) {
      stats.pending_df++;
      if (options.verbose) {
        std::cout << "No external .subchart file found for df node "
                  << std::format("{:x}", df.id) << " in " << options.subcharts_dir << "\n";
      }
      continue;
    }

    auto res = ProcessExternalFile(ext_file, geom, options, next_avail_id, stats);
    if (res.absorbed) {
      replacements[df.id] = std::move(res.replacement_lines);
    }
  }

  if (replacements.empty()) {
    if (options.verbose) {
      std::cout << in_path << ": No rows were absorbed (all external files large or unresolved).\n";
    }
    return true;
  }

  if (options.dry_run) {
    std::cout << "[DRY RUN] Would absorb " << replacements.size()
              << " subtrees into " << out_path << "\n";
    return true;
  }

  // Pass 2: Stream in_path to out_path, replacing absorbed df rows
  infile.open(in_path);
  if (!infile.is_open()) {
    std::cerr << "Error: Cannot reopen " << in_path << " for streaming\n";
    return false;
  }

  std::string tmp_out = out_path + ".tmp";
  std::ofstream outfile(tmp_out);
  if (!outfile.is_open()) {
    std::cerr << "Error: Cannot open " << tmp_out << " for writing\n";
    return false;
  }

  is_first_line = true;
  while (std::getline(infile, line)) {
    if (line.empty()) {
      outfile << "\n";
      continue;
    }
    if (line[0] == '#') {
      outfile << line << "\n";
      continue;
    }

    if (is_first_line) {
      is_first_line = false;
      if (line.rfind("ge ", 0) == 0 || line.rfind("GE ", 0) == 0) {
        outfile << line << "\n";
        continue;
      }
    }

    if (line.rfind("df ", 0) == 0 || line.rfind("DF ", 0) == 0 ||
        line.rfind("di ", 0) == 0 || line.rfind("DI ", 0) == 0) {
      Chart229::Row r = Chart229::Parse(line);
      if (std::holds_alternative<Chart229::DifficultRow>(r)) {
        const auto &df = std::get<Chart229::DifficultRow>(r);
        auto it = replacements.find(df.id);
        if (it != replacements.end()) {
          // Replace df row with absorbed rows!
          for (const auto &rep_line : it->second) {
            outfile << rep_line << "\n";
          }
          continue;
        }
      }
    }

    // Pass through unmodified
    outfile << line << "\n";
  }

  infile.close();
  outfile.close();

  std::filesystem::rename(tmp_out, out_path);
  return true;
}

}  // namespace flatten_charts

#endif  // _RUPERTS_FLATTEN_CHARTS_H
