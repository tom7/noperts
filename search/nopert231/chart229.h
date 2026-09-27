#ifndef _RUPERTS_CHART229_H
#define _RUPERTS_CHART229_H

#include <cstdint>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

// Parser and serializer for Nopert #229 search tree rows and certificates.
// Supports both the compact lowercase hexadecimal format and legacy uppercase decimal format.
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
      DifficultRow>;

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
  static std::string SerializeLegacy(const Row &row);

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
