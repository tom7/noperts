#ifndef _RUPERTS_CHART229_H
#define _RUPERTS_CHART229_H

#include <cstdint>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

// Parser and serializer for Nopert #229 search tree rows and certificates.
// Supports both the compact lowercase hexadecimal format and legacy uppercase decimal format.
//
// -----------------------------------------------------------------------------
// Row ID Semantics and Scoping:
//
// 1. File-Local Scope:
//    Row IDs (id, parent_id, child0..child3) are strictly internal to a single
//    file (e.g. root chart 'chart0.rows.log' or subchart 'chart0.7c9.subchart').
//    Within that file, IDs must be unique and form a consistent tree, but they
//    are not required to be globally unique across different files.
//
// 2. External Boundary IDs ("df" rows):
//    A "df" (difficult) row explicitly creates an external boundary:
//      df <id> <parent_id> <depth>
//    This row declares that the subtree rooted at <id> is expanded externally in
//    a separate subchart file:
//      chart<N>.<id_hex>.subchart
//    where N is the chart index and <id_hex> is the row ID formatted in lowercase
//    hexadecimal (matching the hex format of row IDs).
//
// 3. Subchart Root Geometry ("ge" rows):
//    A subchart file should start with a "ge" (geometry) row specifying the root
//    pose and bounding context for that subtree:
//      ge <id> <parent_id> <depth> <box_depth> <view_depth> <chart> ...
//    The <id> in this "ge" row corresponds directly to the external ID referenced
//    by the parent's "df" row.
//
// 4. Internal Descendants and Splicing:
//    All descendant rows inside the subchart use file-local IDs. When a packer or
//    verifier splices subcharts into a unified certificate (e.g. pack229), internal
//    descendant IDs are renumbered/remapped to fresh IDs to prevent collisions
//    across independently solved subcharts. Only the external boundary ID
//    (matching the subchart filename and "ge" row) is stitched to the parent tree.
// -----------------------------------------------------------------------------
class Chart229 {
 public:
  struct ParseError {
    std::string message;

    bool operator==(const ParseError &other) const = default;
  };

  struct EmptyRow {
    bool operator==(const EmptyRow &other) const = default;
  };

  struct CommentRow {
    std::string text;

    bool operator==(const CommentRow &other) const = default;
  };

  struct CertRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    int winning_triple = 0;
    double margin = 0.0;
    int in0 = 0;
    int in1 = 0;
    int in2 = 0;
    // Cone samples of the candidate pool that winning_triple indexes into
    // (the pool is a function of the view triangle and this). 0 = unknown
    // (legacy rows without the field).
    int cone_samples = 0;

    bool operator==(const CertRow &other) const = default;
  };

  struct MixedComponent {
    int winning_triple = 0;
    double weight = 0.0;
    int in0 = 0;
    int in1 = 0;
    int in2 = 0;

    bool operator==(const MixedComponent &other) const = default;
  };

  struct MixedCertRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    double margin = 0.0;
    std::vector<MixedComponent> components;
    // As in CertRow; 0 = unknown (legacy).
    int cone_samples = 0;

    bool operator==(const MixedCertRow &other) const = default;
  };

  struct SplitRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    int64_t child0 = 0;
    int64_t child1 = 0;

    bool operator==(const SplitRow &other) const = default;
  };

  struct SplitOriginRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    int64_t child0 = 0;
    int64_t child1 = 0;

    bool operator==(const SplitOriginRow &other) const = default;
  };

  struct SplitViewRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    int64_t child0 = 0;
    int64_t child1 = 0;
    int64_t child2 = 0;
    int64_t child3 = 0;

    bool operator==(const SplitViewRow &other) const = default;
  };

  // Radius prune: "pr <id> <parent_id> <depth>"
  struct PruneRadiusRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;

    bool operator==(const PruneRadiusRow &other) const = default;
  };

  // Fundamental symmetry prune: "pf <id> <parent_id> <depth> <fund_dir>"
  struct PruneFundamentalRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    int fund_dir = 1;

    bool operator==(const PruneFundamentalRow &other) const = default;
  };

  // Rigidity tube prune: "tu <id> <parent_id> <depth> <tube_radius>"
  struct TubeRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    double tube_radius = 0.0;

    bool operator==(const TubeRow &other) const = default;
  };

  // Difficult leaf cell: "df <id> <parent_id> <depth>"
  struct DifficultRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;

    bool operator==(const DifficultRow &other) const = default;
  };

  // Geometric context row:
  // Compact lowercase hex:
  //   "ge <id> <parent_id> <depth> <box_depth> <view_depth> <chart> "
  //   "<cx> <cy> <cz> <rx> <ry> <rz> "
  //   "<v0x> <v0y> <v0z> <v1x> <v1y> <v1z> <v2x> <v2y> <v2z> "
  //   "[best_margin]"
  // Legacy decimal:
  //   "GE <id> <parent_id> <depth> <box_depth> <view_depth> <chart> ..."
  struct GeometryRow {
    int64_t id = 0;
    int64_t parent_id = -1;
    int depth = 0;
    int box_depth = 0;
    int view_depth = 0;
    int chart = 0;
    // 3D Cayley box: center (cx, cy, cz) and radii (rx, ry, rz)
    double cx = 0.0, cy = 0.0, cz = 0.0;
    double rx = 0.0, ry = 0.0, rz = 0.0;
    // 2D Projective view triangle: 3 corners in R^3
    double v0x = 0.0, v0y = 0.0, v0z = 0.0;
    double v1x = 0.0, v1y = 0.0, v1z = 0.0;
    double v2x = 0.0, v2y = 0.0, v2z = 0.0;
    // Clearance / best margin (optional, default 0.0)
    double best_margin = 0.0;

    bool operator==(const GeometryRow &other) const = default;
  };

  using Row = std::variant<
      ParseError,
      EmptyRow,
      CommentRow,
      CertRow,
      MixedCertRow,
      SplitRow,
      SplitOriginRow,
      SplitViewRow,
      PruneRadiusRow,
      PruneFundamentalRow,
      TubeRow,
      DifficultRow,
      GeometryRow>;

  // Parses a single line.
  // Leading whitespace and trailing whitespace/newlines (\r, \n) are trimmed.
  // Returns one of the Row variant alternatives.
  static Row Parse(std::string_view line);

  // Serializes each row type to the compact lowercase hex format
  // (without trailing newline).
  static std::string Serialize(const CertRow &row);
  static std::string Serialize(const MixedCertRow &row);
  static std::string Serialize(const SplitRow &row);
  static std::string Serialize(const SplitOriginRow &row);
  static std::string Serialize(const SplitViewRow &row);
  static std::string Serialize(const PruneRadiusRow &row);
  static std::string Serialize(const PruneFundamentalRow &row);
  static std::string Serialize(const TubeRow &row);
  static std::string Serialize(const DifficultRow &row);
  static std::string Serialize(const GeometryRow &row);

  // Serializes any Row variant to the compact lowercase hex format.
  // EmptyRow serializes to "", CommentRow to "# <text>", ParseError
  // to error message.
  static std::string Serialize(const Row &row);

  // Legacy decimal serialization for compatibility and testing.
  static std::string SerializeLegacy(const CertRow &row);
  static std::string SerializeLegacy(const MixedCertRow &row);
  static std::string SerializeLegacy(const SplitRow &row);
  static std::string SerializeLegacy(const SplitOriginRow &row);
  static std::string SerializeLegacy(const SplitViewRow &row);
  static std::string SerializeLegacy(const PruneRadiusRow &row);
  static std::string SerializeLegacy(const PruneFundamentalRow &row);
  static std::string SerializeLegacy(const TubeRow &row);
  static std::string SerializeLegacy(const DifficultRow &row);
  static std::string SerializeLegacy(const GeometryRow &row);
  static std::string SerializeLegacy(const Row &row);

  // Serializes to the untagged legacy .difficult line format (with trailing newline):
  // "<id> <parent_id> <depth> <box_depth> <view_depth> <chart> <cx> ... <best_margin>\n"
  static std::string SerializeLegacyDifficult(const GeometryRow &row);

  // Parses a single line from a legacy .difficult file.
  // Handles blank lines (EmptyRow), comments (CommentRow), lines starting with
  // 'ge' or 'GE', and legacy tagless 22-token decimal lines.
  static Row ParseLegacyDifficultLine(std::string_view line);

  // Parses a full legacy .difficult file from disk into GeometryRow items.
  // Skips comments and empty lines. If error_msg is non-null and an error occurs,
  // *error_msg is set to the first error encountered.
  static std::vector<GeometryRow> ParseLegacyDifficultFile(
      const std::string &path, std::string *error_msg = nullptr);

  // Parses legacy .difficult content from a string buffer.
  static std::vector<GeometryRow> ParseLegacyDifficultContent(
      std::string_view content, std::string *error_msg = nullptr);

  template <class... Ts>
  struct Overloaded : Ts... {
    using Ts::operator()...;
  };

  // Helper inspection utilities.
  static bool IsError(const Row &row) {
    return std::holds_alternative<ParseError>(row);
  }

  static bool IsEmptyOrComment(const Row &row) {
    return std::holds_alternative<EmptyRow>(row) ||
           std::holds_alternative<CommentRow>(row);
  }

  // Returns node ID, or -1 if the row does not have a node ID.
  static int64_t GetId(const Row &row);
  // Returns parent ID, or -1 if the row does not have a parent ID.
  static int64_t GetParentId(const Row &row);
  // Returns node depth, or 0 if the row does not have a depth.
  static int GetDepth(const Row &row);
};

#endif  // _RUPERTS_CHART229_H
