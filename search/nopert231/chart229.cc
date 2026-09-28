#include "chart229.h"

#include <charconv>
#include <format>
#include <string>
#include <string_view>
#include <system_error>
#include <type_traits>

#include "util.h"

namespace {

std::string_view TrimWhitespace(std::string_view s) {
  Util::RemoveOuterWhitespace(&s);
  return s;
}

std::string_view NextToken(std::string_view &rest) {
  Util::RemoveLeadingWhitespace(&rest);
  if (rest.empty()) return {};
  std::string_view tok = Util::NextToken(&rest, ' ');
  if (size_t pos = tok.find_first_of("\t\r\n"); pos != std::string_view::npos) {
    rest = std::string_view(tok.data() + pos, (rest.data() + rest.size()) - (tok.data() + pos));
    tok = tok.substr(0, pos);
  }
  Util::RemoveLeadingWhitespace(&rest);
  return tok;
}

template <typename T>
bool ParseInt(std::string_view tok, int base, T &out) {
  if (tok.empty()) return false;
  if (tok.front() == '+') {
    tok.remove_prefix(1);
    if (tok.empty()) return false;
  }
  if (base == 16) {
    if (tok.starts_with("-0x") || tok.starts_with("-0X")) {
      std::string s = "-" + std::string(tok.substr(3));
      auto res = std::from_chars(s.data(), s.data() + s.size(), out, 16);
      return res.ec == std::errc() && res.ptr == s.data() + s.size();
    } else if (tok.starts_with("0x") || tok.starts_with("0X")) {
      tok.remove_prefix(2);
    }
  }
  auto res = std::from_chars(tok.data(), tok.data() + tok.size(), out, base);
  return res.ec == std::errc() && res.ptr == tok.data() + tok.size();
}

bool ParseFloat(std::string_view tok, bool hex_mode, double &out) {
  if (tok.empty()) return false;
  if (tok.front() == '+') {
    tok.remove_prefix(1);
    if (tok.empty()) return false;
  }
  if (hex_mode) {
    if (tok.starts_with("-0x") || tok.starts_with("-0X")) {
      std::string s = "-" + std::string(tok.substr(3));
      auto res = std::from_chars(s.data(), s.data() + s.size(), out, std::chars_format::hex);
      return res.ec == std::errc() && res.ptr == s.data() + s.size();
    } else if (tok.starts_with("0x") || tok.starts_with("0X")) {
      tok.remove_prefix(2);
    }
    auto res = std::from_chars(tok.data(), tok.data() + tok.size(), out, std::chars_format::hex);
    return res.ec == std::errc() && res.ptr == tok.data() + tok.size();
  } else {
    auto res = std::from_chars(tok.data(), tok.data() + tok.size(), out, std::chars_format::general);
    return res.ec == std::errc() && res.ptr == tok.data() + tok.size();
  }
}

template <typename T>
void AppendHexInt(std::string &out, T val) {
  char buf[32];
  auto res = std::to_chars(buf, buf + sizeof(buf), val, 16);
  out.append(buf, res.ptr);
}

void AppendHexDouble(std::string &out, double val) {
  char buf[64];
  auto res = std::to_chars(buf, buf + sizeof(buf), val, std::chars_format::hex);
  out.append(buf, res.ptr);
}

void AppendDecimalDouble(std::string &out, double val) {
  out += std::format("{:.17g}", val);
}

}  // namespace

Chart229::Row Chart229::Parse(std::string_view line) {
  std::string_view trimmed = TrimWhitespace(line);
  if (trimmed.empty()) {
    return EmptyRow{};
  }
  if (trimmed.front() == '#') {
    std::string_view comment = trimmed.substr(1);
    Util::RemoveLeadingWhitespace(&comment);
    return CommentRow{std::string(comment)};
  }

  std::string_view rest = trimmed;
  std::string_view tag = NextToken(rest);
  if (tag.empty()) {
    return EmptyRow{};
  }

  bool hex_mode = (tag.front() >= 'a' && tag.front() <= 'z');
  int base = hex_mode ? 16 : 10;

  int64_t id = 0, parent_id = -1;
  int depth = 0;

  auto ParseNodeHeader = [&]() -> bool {
    std::string_view id_tok = NextToken(rest);
    std::string_view pid_tok = NextToken(rest);
    std::string_view depth_tok = NextToken(rest);
    if (id_tok.empty() || pid_tok.empty() || depth_tok.empty()) {
      return false;
    }
    return ParseInt(id_tok, base, id) &&
           ParseInt(pid_tok, base, parent_id) &&
           ParseInt(depth_tok, base, depth);
  };

  if (tag == "ce" || tag == "CE" || tag == "CERT") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    std::string_view trip_tok = NextToken(rest);
    std::string_view margin_tok = NextToken(rest);
    std::string_view in0_tok = NextToken(rest);
    std::string_view in1_tok = NextToken(rest);
    std::string_view in2_tok = NextToken(rest);

    int triple = 0, in0 = 0, in1 = 0, in2 = 0;
    double margin = 0.0;
    if (trip_tok.empty() || margin_tok.empty() ||
        in0_tok.empty() || in1_tok.empty() || in2_tok.empty() ||
        !ParseInt(trip_tok, base, triple) ||
        !ParseFloat(margin_tok, hex_mode, margin) ||
        !ParseInt(in0_tok, base, in0) ||
        !ParseInt(in1_tok, base, in1) ||
        !ParseInt(in2_tok, base, in2)) {
      return ParseError{std::format("Malformed {} row parameters: '{}'", tag, line)};
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return CertRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .winning_triple = triple,
        .margin = margin,
        .in0 = in0,
        .in1 = in1,
        .in2 = in2,
    };
  }

  if (tag == "mx" || tag == "MX") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    std::string_view k_tok = NextToken(rest);
    std::string_view margin_tok = NextToken(rest);
    int num_components = 0;
    double margin = 0.0;
    if (k_tok.empty() || margin_tok.empty() ||
        !ParseInt(k_tok, base, num_components) ||
        !ParseFloat(margin_tok, hex_mode, margin) ||
        num_components < 0 || num_components > 64) {
      return ParseError{std::format("Malformed {} component header: '{}'", tag, line)};
    }

    std::vector<MixedComponent> comps;
    comps.reserve(num_components);
    for (int k = 0; k < num_components; k++) {
      std::string_view trip_tok = NextToken(rest);
      std::string_view weight_tok = NextToken(rest);
      std::string_view in0_tok = NextToken(rest);
      std::string_view in1_tok = NextToken(rest);
      std::string_view in2_tok = NextToken(rest);

      int triple = 0, in0 = 0, in1 = 0, in2 = 0;
      double weight = 0.0;
      if (trip_tok.empty() || weight_tok.empty() ||
          in0_tok.empty() || in1_tok.empty() || in2_tok.empty() ||
          !ParseInt(trip_tok, base, triple) ||
          !ParseFloat(weight_tok, hex_mode, weight) ||
          !ParseInt(in0_tok, base, in0) ||
          !ParseInt(in1_tok, base, in1) ||
          !ParseInt(in2_tok, base, in2)) {
        return ParseError{std::format("Malformed {} component {}: '{}'", tag, k, line)};
      }
      comps.push_back({
          .winning_triple = triple,
          .weight = weight,
          .in0 = in0,
          .in1 = in1,
          .in2 = in2,
      });
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return MixedCertRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .margin = margin,
        .components = std::move(comps),
    };
  }

  if (tag == "sp" || tag == "SP" || tag == "SPLIT") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    std::string_view c0_tok = NextToken(rest);
    std::string_view c1_tok = NextToken(rest);
    int64_t c0 = 0, c1 = 0;
    if (c0_tok.empty() || c1_tok.empty() ||
        !ParseInt(c0_tok, base, c0) ||
        !ParseInt(c1_tok, base, c1)) {
      return ParseError{std::format("Malformed {} child IDs: '{}'", tag, line)};
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return SplitRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .child0 = c0,
        .child1 = c1,
    };
  }

  if (tag == "so" || tag == "SO" || tag == "SPLIT_ORIGIN") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    std::string_view c0_tok = NextToken(rest);
    std::string_view c1_tok = NextToken(rest);
    int64_t c0 = 0, c1 = 0;
    if (c0_tok.empty() || c1_tok.empty() ||
        !ParseInt(c0_tok, base, c0) ||
        !ParseInt(c1_tok, base, c1)) {
      return ParseError{std::format("Malformed {} child IDs: '{}'", tag, line)};
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return SplitOriginRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .child0 = c0,
        .child1 = c1,
    };
  }

  if (tag == "sv" || tag == "SV" || tag == "SPLIT_VIEW") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    std::string_view c0_tok = NextToken(rest);
    std::string_view c1_tok = NextToken(rest);
    std::string_view c2_tok = NextToken(rest);
    std::string_view c3_tok = NextToken(rest);
    int64_t c0 = 0, c1 = 0, c2 = 0, c3 = 0;
    if (c0_tok.empty() || c1_tok.empty() || c2_tok.empty() || c3_tok.empty() ||
        !ParseInt(c0_tok, base, c0) ||
        !ParseInt(c1_tok, base, c1) ||
        !ParseInt(c2_tok, base, c2) ||
        !ParseInt(c3_tok, base, c3)) {
      return ParseError{std::format("Malformed {} child IDs: '{}'", tag, line)};
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return SplitViewRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .child0 = c0,
        .child1 = c1,
        .child2 = c2,
        .child3 = c3,
    };
  }

  if (tag == "pr") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed pr header: '{}'", line)};
    }
    std::string_view next_tok = NextToken(rest);
    if (next_tok.empty() || next_tok == "r" || next_tok == "R" ||
        next_tok == "ra" || next_tok == "RA" ||
        next_tok == "radius" || next_tok == "RADIUS") {
      if (!rest.empty()) {
        return ParseError{std::format("Extra tokens on pr row: '{}'", line)};
      }
      return PruneRadiusRow{
          .id = id,
          .parent_id = parent_id,
          .depth = depth,
      };
    } else if (next_tok == "f" || next_tok == "F" ||
               next_tok == "fu" || next_tok == "FU" ||
               next_tok == "fundamental" || next_tok == "FUNDAMENTAL") {
      std::string_view dir_tok = NextToken(rest);
      int fdir = 1;
      if (dir_tok.empty() || !ParseInt(dir_tok, 16, fdir)) {
        return ParseError{std::format("Malformed direction on pf/pr fundamental row: '{}'", line)};
      }
      if (!rest.empty()) {
        return ParseError{std::format("Extra tokens on fundamental prune row: '{}'", line)};
      }
      return PruneFundamentalRow{
          .id = id,
          .parent_id = parent_id,
          .depth = depth,
          .fund_dir = fdir,
      };
    } else {
      return ParseError{std::format("Unrecognized token '{}' on pr row: '{}'", next_tok, line)};
    }
  }

  if (tag == "pf" || tag == "PF") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed pf header: '{}'", line)};
    }
    std::string_view dir_tok = NextToken(rest);
    if (dir_tok == "f" || dir_tok == "F" ||
        dir_tok == "fu" || dir_tok == "FU" ||
        dir_tok == "fundamental" || dir_tok == "FUNDAMENTAL") {
      dir_tok = NextToken(rest);
    }
    int fdir = 1;
    if (dir_tok.empty() || !ParseInt(dir_tok, base, fdir)) {
      return ParseError{std::format("Malformed pf direction: '{}'", line)};
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on pf row: '{}'", line)};
    }
    return PruneFundamentalRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .fund_dir = fdir,
    };
  }

  if (tag == "PR" || tag == "PRUNE") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed PR header: '{}'", line)};
    }
    std::string_view kind_tok = NextToken(rest);
    if (kind_tok == "RADIUS" || kind_tok == "RA" || kind_tok == "R" || kind_tok == "r") {
      if (!rest.empty()) {
        return ParseError{std::format("Extra tokens on PR RADIUS row: '{}'", line)};
      }
      return PruneRadiusRow{
          .id = id,
          .parent_id = parent_id,
          .depth = depth,
      };
    } else if (kind_tok == "FUNDAMENTAL" || kind_tok == "FU" || kind_tok == "F" || kind_tok == "f") {
      std::string_view dir_tok = NextToken(rest);
      int fdir = 1;
      if (dir_tok.empty() || !ParseInt(dir_tok, 10, fdir)) {
        return ParseError{std::format("Malformed PR FUNDAMENTAL direction: '{}'", line)};
      }
      if (!rest.empty()) {
        return ParseError{std::format("Extra tokens on PR FUNDAMENTAL row: '{}'", line)};
      }
      return PruneFundamentalRow{
          .id = id,
          .parent_id = parent_id,
          .depth = depth,
          .fund_dir = fdir,
      };
    } else {
      return ParseError{std::format("Unrecognized PR prune kind '{}': '{}'", kind_tok, line)};
    }
  }

  if (tag == "tu" || tag == "TU" || tag == "TUBE") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    std::string_view r_tok = NextToken(rest);
    double r = 0.0;
    if (r_tok.empty() || !ParseFloat(r_tok, hex_mode, r)) {
      return ParseError{std::format("Malformed {} tube radius: '{}'", tag, line)};
    }
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return TubeRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
        .tube_radius = r,
    };
  }

  if (tag == "df" || tag == "DF" || tag == "DI" || tag == "DIFFICULT") {
    if (!ParseNodeHeader()) {
      return ParseError{std::format("Malformed {} header: '{}'", tag, line)};
    }
    // Margin is optional on DF rows (e.g. older logs or debug outputs).
    std::string_view opt_margin = NextToken(rest);
    (void)opt_margin;
    if (!rest.empty()) {
      return ParseError{std::format("Extra tokens on {} row: '{}'", tag, line)};
    }
    return DifficultRow{
        .id = id,
        .parent_id = parent_id,
        .depth = depth,
    };
  }

  return ParseError{std::format("Unrecognized row tag '{}' on line: '{}'", tag, line)};
}

std::string Chart229::Serialize(const CertRow &row) {
  std::string out = "ce ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexInt(out, row.winning_triple);
  out += ' ';
  AppendHexDouble(out, row.margin);
  out += ' ';
  AppendHexInt(out, row.in0);
  out += ' ';
  AppendHexInt(out, row.in1);
  out += ' ';
  AppendHexInt(out, row.in2);
  return out;
}

std::string Chart229::Serialize(const MixedCertRow &row) {
  std::string out = "mx ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexInt(out, (int)row.components.size());
  out += ' ';
  AppendHexDouble(out, row.margin);
  for (const auto &comp : row.components) {
    out += ' ';
    AppendHexInt(out, comp.winning_triple);
    out += ' ';
    AppendHexDouble(out, comp.weight);
    out += ' ';
    AppendHexInt(out, comp.in0);
    out += ' ';
    AppendHexInt(out, comp.in1);
    out += ' ';
    AppendHexInt(out, comp.in2);
  }
  return out;
}

std::string Chart229::Serialize(const SplitRow &row) {
  std::string out = "sp ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexInt(out, row.child0);
  out += ' ';
  AppendHexInt(out, row.child1);
  return out;
}

std::string Chart229::Serialize(const SplitOriginRow &row) {
  std::string out = "so ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexInt(out, row.child0);
  out += ' ';
  AppendHexInt(out, row.child1);
  return out;
}

std::string Chart229::Serialize(const SplitViewRow &row) {
  std::string out = "sv ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexInt(out, row.child0);
  out += ' ';
  AppendHexInt(out, row.child1);
  out += ' ';
  AppendHexInt(out, row.child2);
  out += ' ';
  AppendHexInt(out, row.child3);
  return out;
}

std::string Chart229::Serialize(const PruneRadiusRow &row) {
  std::string out = "pr ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  return out;
}

std::string Chart229::Serialize(const PruneFundamentalRow &row) {
  std::string out = "pf ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexInt(out, row.fund_dir);
  return out;
}

std::string Chart229::Serialize(const TubeRow &row) {
  std::string out = "tu ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  out += ' ';
  AppendHexDouble(out, row.tube_radius);
  return out;
}

std::string Chart229::Serialize(const DifficultRow &row) {
  std::string out = "df ";
  AppendHexInt(out, row.id);
  out += ' ';
  AppendHexInt(out, row.parent_id);
  out += ' ';
  AppendHexInt(out, row.depth);
  return out;
}

std::string Chart229::Serialize(const Row &row) {
  return std::visit([](const auto &r) -> std::string {
    using T = std::decay_t<decltype(r)>;
    if constexpr (std::is_same_v<T, ParseError>) {
      throw std::runtime_error("Attempt to serialize a ParseError: " + r.message);
    } else if constexpr (std::is_same_v<T, EmptyRow>) {
      return "";
    } else if constexpr (std::is_same_v<T, CommentRow>) {
      return "# " + r.text;
    } else {
      return Chart229::Serialize(r);
    }
  }, row);
}

std::string Chart229::SerializeLegacy(const CertRow &row) {
  std::string out = std::format("CE {} {} {} {} ",
                                row.id, row.parent_id, row.depth,
                                row.winning_triple);
  AppendDecimalDouble(out, row.margin);
  out += std::format(" {} {} {}", row.in0, row.in1, row.in2);
  return out;
}

std::string Chart229::SerializeLegacy(const MixedCertRow &row) {
  std::string out = std::format("MX {} {} {} {} ",
                                row.id, row.parent_id, row.depth,
                                row.components.size());
  AppendDecimalDouble(out, row.margin);
  for (const auto &comp : row.components) {
    out += std::format(" {} ", comp.winning_triple);
    AppendDecimalDouble(out, comp.weight);
    out += std::format(" {} {} {}", comp.in0, comp.in1, comp.in2);
  }
  return out;
}

std::string Chart229::SerializeLegacy(const SplitRow &row) {
  return std::format("SP {} {} {} {} {}",
                     row.id, row.parent_id, row.depth, row.child0, row.child1);
}

std::string Chart229::SerializeLegacy(const SplitOriginRow &row) {
  return std::format("SO {} {} {} {} {}",
                     row.id, row.parent_id, row.depth, row.child0, row.child1);
}

std::string Chart229::SerializeLegacy(const SplitViewRow &row) {
  return std::format("SV {} {} {} {} {} {} {}",
                     row.id, row.parent_id, row.depth, row.child0,
                     row.child1, row.child2, row.child3);
}

std::string Chart229::SerializeLegacy(const PruneRadiusRow &row) {
  return std::format("PR {} {} {} RADIUS", row.id, row.parent_id, row.depth);
}

std::string Chart229::SerializeLegacy(const PruneFundamentalRow &row) {
  return std::format("PR {} {} {} FUNDAMENTAL {}", row.id, row.parent_id, row.depth, row.fund_dir);
}

std::string Chart229::SerializeLegacy(const TubeRow &row) {
  std::string out = std::format("TU {} {} {} ", row.id, row.parent_id, row.depth);
  AppendDecimalDouble(out, row.tube_radius);
  return out;
}

std::string Chart229::SerializeLegacy(const DifficultRow &row) {
  return std::format("DF {} {} {}", row.id, row.parent_id, row.depth);
}

std::string Chart229::SerializeLegacy(const Row &row) {
  return std::visit([](const auto &r) -> std::string {
    using T = std::decay_t<decltype(r)>;
    if constexpr (std::is_same_v<T, ParseError>) {
      return r.message;
    } else if constexpr (std::is_same_v<T, EmptyRow>) {
      return "";
    } else if constexpr (std::is_same_v<T, CommentRow>) {
      return "# " + r.text;
    } else {
      return Chart229::SerializeLegacy(r);
    }
  }, row);
}

int64_t Chart229::GetId(const Row &row) {
  return std::visit([](const auto &r) -> int64_t {
    using T = std::decay_t<decltype(r)>;
    if constexpr (std::is_same_v<T, ParseError> ||
                  std::is_same_v<T, EmptyRow> ||
                  std::is_same_v<T, CommentRow>) {
      return -1;
    } else {
      return r.id;
    }
  }, row);
}

int64_t Chart229::GetParentId(const Row &row) {
  return std::visit([](const auto &r) -> int64_t {
    using T = std::decay_t<decltype(r)>;
    if constexpr (std::is_same_v<T, ParseError> ||
                  std::is_same_v<T, EmptyRow> ||
                  std::is_same_v<T, CommentRow>) {
      return -1;
    } else {
      return r.parent_id;
    }
  }, row);
}

int Chart229::GetDepth(const Row &row) {
  return std::visit([](const auto &r) -> int {
    using T = std::decay_t<decltype(r)>;
    if constexpr (std::is_same_v<T, ParseError> ||
                  std::is_same_v<T, EmptyRow> ||
                  std::is_same_v<T, CommentRow>) {
      return 0;
    } else {
      return r.depth;
    }
  }, row);
}
