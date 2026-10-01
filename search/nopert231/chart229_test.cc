#include "chart229.h"

#include <cmath>
#include <iostream>
#include <string>
#include <variant>
#include <vector>

#include "base/logging.h"

static void TestCertRow() {
  printf("Testing CertRow...\n");

  // 1. Legacy decimal parsing (CE and CERT tags)
  std::string_view legacy_ce = "CE 1993 1975 10 1805 0.00063884886633153561 7 13 1 8";
  auto r1 = Chart229::Parse(legacy_ce);
  CHECK(std::holds_alternative<Chart229::CertRow>(r1));
  const auto &c1 = std::get<Chart229::CertRow>(r1);
  CHECK(c1.id == 1993);
  CHECK(c1.parent_id == 1975);
  CHECK(c1.depth == 10);
  CHECK(c1.winning_triple == 1805);
  CHECK(std::abs(c1.margin - 0.00063884886633153561) < 1e-18);
  CHECK(c1.in0 == 7 && c1.in1 == 13 && c1.in2 == 1);

  std::string_view legacy_cert = "CERT 100 50 5 12 0.001 1 2 3 8";
  auto r2 = Chart229::Parse(legacy_cert);
  CHECK(std::holds_alternative<Chart229::CertRow>(r2));
  const auto &c2 = std::get<Chart229::CertRow>(r2);
  CHECK(c2.id == 100 && c2.parent_id == 50 && c2.depth == 5);

  // 2. Compact hex parsing (lowercase ce)
  std::string_view hex_ce = "ce 7c9 7b7 a 70d 1.4ef0d7e762624p-11 7 d 1 8";
  auto r3 = Chart229::Parse(hex_ce);
  CHECK(std::holds_alternative<Chart229::CertRow>(r3));
  const auto &c3 = std::get<Chart229::CertRow>(r3);
  CHECK(c3.id == 1993);
  CHECK(c3.parent_id == 1975);
  CHECK(c3.depth == 10);
  CHECK(c3.winning_triple == 1805);
  CHECK(c3.in0 == 7 && c3.in1 == 13 && c3.in2 == 1);
  CHECK(c3.margin == c1.margin);

  // 3. Alternative hex float syntax (from SMALLER_CERTS.txt example: unnormalized mantissa)
  std::string_view hex_ce_alt = "ce 7c9 7b7 a 70d a.7786bf3b131200dp-14 7 d 1 8";
  auto r4 = Chart229::Parse(hex_ce_alt);
  CHECK(std::holds_alternative<Chart229::CertRow>(r4));
  const auto &c4 = std::get<Chart229::CertRow>(r4);
  CHECK(std::abs(c4.margin - c1.margin) < 1e-18);

  // 4. Serialization to compact lowercase hex
  std::string serialized = Chart229::Serialize(c1);
  CHECK(serialized == "ce 7c9 7b7 a 70d 1.4ef0d7e762624p-11 7 d 1 8");

  // 5. Round trip
  auto r_rt = Chart229::Parse(serialized);
  CHECK(std::holds_alternative<Chart229::CertRow>(r_rt));
  CHECK(std::get<Chart229::CertRow>(r_rt) == c1);

  // 6. Root node with parent_id = -1; cone_samples is written in hex.
  Chart229::CertRow root_cert{
      .id = 0,
      .parent_id = -1,
      .depth = 0,
      .winning_triple = 42,
      .margin = 0.5,
      .in0 = 1,
      .in1 = 2,
      .in2 = 3,
      .cone_samples = 12,
  };
  std::string root_s = Chart229::Serialize(root_cert);
  CHECK(root_s == "ce 0 -1 0 2a 1p-1 1 2 3 c");
  auto root_parsed = Chart229::Parse(root_s);
  CHECK(std::holds_alternative<Chart229::CertRow>(root_parsed));
  CHECK(std::get<Chart229::CertRow>(root_parsed) == root_cert);
  auto root_legacy = Chart229::Parse(Chart229::SerializeLegacy(root_cert));
  CHECK(std::holds_alternative<Chart229::CertRow>(root_legacy));
  CHECK(std::get<Chart229::CertRow>(root_legacy) == root_cert);

  // 7. cone_samples (the pool the triple index refers to) is required and positive.
  CHECK(Chart229::IsError(Chart229::Parse("ce 0 -1 0 2a 1p-1 1 2 3")));
  CHECK(Chart229::IsError(Chart229::Parse("ce 0 -1 0 2a 1p-1 1 2 3 0")));

  printf("  CertRow tests PASSED.\n");
}

static void TestMixedCertRow() {
  printf("Testing MixedCertRow...\n");

  // 1. Legacy decimal parsing
  std::string_view legacy_mx = "MX 18 3 4 2 0.0009765625 256 0.5 1 2 3 257 0.5 4 5 6 8";
  auto r1 = Chart229::Parse(legacy_mx);
  CHECK(std::holds_alternative<Chart229::MixedCertRow>(r1));
  const auto &m1 = std::get<Chart229::MixedCertRow>(r1);
  CHECK(m1.id == 18);
  CHECK(m1.parent_id == 3);
  CHECK(m1.depth == 4);
  CHECK(m1.margin == 0.0009765625);
  CHECK(m1.components.size() == 2);
  CHECK(m1.components[0].winning_triple == 256);
  CHECK(m1.components[0].weight == 0.5);
  CHECK(m1.components[0].in0 == 1 && m1.components[0].in1 == 2 && m1.components[0].in2 == 3);
  CHECK(m1.components[1].winning_triple == 257);
  CHECK(m1.components[1].weight == 0.5);
  CHECK(m1.components[1].in0 == 4 && m1.components[1].in1 == 5 && m1.components[1].in2 == 6);

  // 2. Compact hex serialization
  std::string s_hex = Chart229::Serialize(m1);
  CHECK(s_hex == "mx 12 3 4 2 1p-10 100 1p-1 1 2 3 101 1p-1 4 5 6 8");

  // 3. Compact hex parsing & round trip
  auto r2 = Chart229::Parse(s_hex);
  CHECK(std::holds_alternative<Chart229::MixedCertRow>(r2));
  CHECK(std::get<Chart229::MixedCertRow>(r2) == m1);

  // 4. cone_samples is parsed (decimal 8 in the legacy row) and required.
  CHECK(m1.cone_samples == 8);
  CHECK(Chart229::IsError(Chart229::Parse("mx 12 3 4 2 1p-10 100 1p-1 1 2 3 101 1p-1 4 5 6")));

  printf("  MixedCertRow tests PASSED.\n");
}

static void TestSplitRows() {
  printf("Testing SplitRow, SplitOriginRow, SplitViewRow...\n");

  // 1. SplitRow
  auto sp_legacy = Chart229::Parse("SP 16 5 3 32 33");
  CHECK(std::holds_alternative<Chart229::SplitRow>(sp_legacy));
  const auto &sp = std::get<Chart229::SplitRow>(sp_legacy);
  CHECK(sp.id == 16 && sp.parent_id == 5 && sp.depth == 3 && sp.child0 == 32 && sp.child1 == 33);
  CHECK(Chart229::Serialize(sp) == "sp 10 5 3 20 21");
  CHECK(std::get<Chart229::SplitRow>(Chart229::Parse("sp 10 5 3 20 21")) == sp);

  // 2. SplitOriginRow
  auto so_legacy = Chart229::Parse("SO 16 5 3 32 33");
  CHECK(std::holds_alternative<Chart229::SplitOriginRow>(so_legacy));
  const auto &so = std::get<Chart229::SplitOriginRow>(so_legacy);
  CHECK(so.id == 16 && so.parent_id == 5 && so.depth == 3 && so.child0 == 32 && so.child1 == 33);
  CHECK(Chart229::Serialize(so) == "so 10 5 3 20 21");
  CHECK(std::get<Chart229::SplitOriginRow>(Chart229::Parse("so 10 5 3 20 21")) == so);

  // 3. SplitViewRow
  auto sv_legacy = Chart229::Parse("SV 16 5 3 32 33 34 35");
  CHECK(std::holds_alternative<Chart229::SplitViewRow>(sv_legacy));
  const auto &sv = std::get<Chart229::SplitViewRow>(sv_legacy);
  CHECK(sv.id == 16 && sv.child0 == 32 && sv.child1 == 33 && sv.child2 == 34 && sv.child3 == 35);
  CHECK(Chart229::Serialize(sv) == "sv 10 5 3 20 21 22 23");
  CHECK(std::get<Chart229::SplitViewRow>(Chart229::Parse("sv 10 5 3 20 21 22 23")) == sv);

  printf("  Split row tests PASSED.\n");
}

static void TestPruneRows() {
  printf("Testing PruneRadiusRow and PruneFundamentalRow (pr and pf)...\n");

  // 1. Legacy PR RADIUS
  auto pr_legacy1 = Chart229::Parse("PR 123 45 6 RADIUS");
  CHECK(std::holds_alternative<Chart229::PruneRadiusRow>(pr_legacy1));
  const auto &pr1 = std::get<Chart229::PruneRadiusRow>(pr_legacy1);
  CHECK(pr1.id == 123 && pr1.parent_id == 45 && pr1.depth == 6);

  auto pr_legacy2 = Chart229::Parse("PR 123 45 6 RA");
  CHECK(std::holds_alternative<Chart229::PruneRadiusRow>(pr_legacy2));
  CHECK(std::get<Chart229::PruneRadiusRow>(pr_legacy2) == pr1);

  // 2. Compact hex pr (no trailing r)
  std::string pr_hex = Chart229::Serialize(pr1);
  CHECK(pr_hex == "pr 7b 2d 6");
  auto pr_parsed = Chart229::Parse(pr_hex);
  CHECK(std::holds_alternative<Chart229::PruneRadiusRow>(pr_parsed));
  CHECK(std::get<Chart229::PruneRadiusRow>(pr_parsed) == pr1);

  // 3. Compact hex pr with optional trailing token tolerated
  auto pr_tolerated = Chart229::Parse("pr 7b 2d 6 r");
  CHECK(std::holds_alternative<Chart229::PruneRadiusRow>(pr_tolerated));
  CHECK(std::get<Chart229::PruneRadiusRow>(pr_tolerated) == pr1);

  // 4. Legacy PR FUNDAMENTAL
  auto pf_legacy1 = Chart229::Parse("PR 123 45 6 FUNDAMENTAL 2");
  CHECK(std::holds_alternative<Chart229::PruneFundamentalRow>(pf_legacy1));
  const auto &pf1 = std::get<Chart229::PruneFundamentalRow>(pf_legacy1);
  CHECK(pf1.id == 123 && pf1.parent_id == 45 && pf1.depth == 6 && pf1.fund_dir == 2);

  auto pf_legacy2 = Chart229::Parse("PR 123 45 6 FU 2");
  CHECK(std::holds_alternative<Chart229::PruneFundamentalRow>(pf_legacy2));
  CHECK(std::get<Chart229::PruneFundamentalRow>(pf_legacy2) == pf1);

  // 5. Compact hex pf (no trailing f)
  std::string pf_hex = Chart229::Serialize(pf1);
  CHECK(pf_hex == "pf 7b 2d 6 2");
  auto pf_parsed = Chart229::Parse(pf_hex);
  CHECK(std::holds_alternative<Chart229::PruneFundamentalRow>(pf_parsed));
  CHECK(std::get<Chart229::PruneFundamentalRow>(pf_parsed) == pf1);

  // 6. Compact hex pf with optional f token tolerated
  auto pf_tolerated1 = Chart229::Parse("pf 7b 2d 6 f 2");
  CHECK(std::holds_alternative<Chart229::PruneFundamentalRow>(pf_tolerated1));
  CHECK(std::get<Chart229::PruneFundamentalRow>(pf_tolerated1) == pf1);

  auto pf_tolerated2 = Chart229::Parse("pr 7b 2d 6 f 2");
  CHECK(std::holds_alternative<Chart229::PruneFundamentalRow>(pf_tolerated2));
  CHECK(std::get<Chart229::PruneFundamentalRow>(pf_tolerated2) == pf1);

  printf("  Prune row tests PASSED.\n");
}

static void TestTubeAndDifficultRows() {
  printf("Testing TubeRow and DifficultRow...\n");

  // 1. TubeRow
  auto tu_legacy = Chart229::Parse("TU 1 0 1 0.0001");
  CHECK(std::holds_alternative<Chart229::TubeRow>(tu_legacy));
  const auto &tu = std::get<Chart229::TubeRow>(tu_legacy);
  CHECK(tu.id == 1 && tu.parent_id == 0 && tu.depth == 1);
  CHECK(std::abs(tu.tube_radius - 0.0001) < 1e-15);

  std::string tu_hex = Chart229::Serialize(tu);
  CHECK(tu_hex == "tu 1 0 1 1.a36e2eb1c432dp-14");
  auto tu_parsed = Chart229::Parse(tu_hex);
  CHECK(std::holds_alternative<Chart229::TubeRow>(tu_parsed));
  CHECK(std::get<Chart229::TubeRow>(tu_parsed) == tu);

  // 2. DifficultRow
  auto df_legacy = Chart229::Parse("DF 256 80 18");
  CHECK(std::holds_alternative<Chart229::DifficultRow>(df_legacy));
  const auto &df = std::get<Chart229::DifficultRow>(df_legacy);
  CHECK(df.id == 256 && df.parent_id == 80 && df.depth == 18);

  std::string df_hex = Chart229::Serialize(df);
  CHECK(df_hex == "df 100 50 12");
  auto df_parsed = Chart229::Parse(df_hex);
  CHECK(std::holds_alternative<Chart229::DifficultRow>(df_parsed));
  CHECK(std::get<Chart229::DifficultRow>(df_parsed) == df);

  printf("  Tube and Difficult row tests PASSED.\n");
}

static void TestCommentsAndUtilities() {
  printf("Testing comments, blank lines, and utilities...\n");

  // Empty lines
  auto e1 = Chart229::Parse("");
  CHECK(std::holds_alternative<Chart229::EmptyRow>(e1));
  CHECK(Chart229::IsEmptyOrComment(e1));

  auto e2 = Chart229::Parse("   \t  \r\n");
  CHECK(std::holds_alternative<Chart229::EmptyRow>(e2));
  CHECK(Chart229::IsEmptyOrComment(e2));

  // Comments
  auto c1 = Chart229::Parse("# search checkpoint at node 500");
  CHECK(std::holds_alternative<Chart229::CommentRow>(c1));
  CHECK(std::get<Chart229::CommentRow>(c1).text == "search checkpoint at node 500");
  CHECK(Chart229::IsEmptyOrComment(c1));

  // Node ID/Parent/Depth utilities
  auto row_cert = Chart229::Parse("ce 7c9 7b7 a 70d 1.4ef0d7e762624p-11 7 d 1 8");
  CHECK(Chart229::GetId(row_cert) == 1993);
  CHECK(Chart229::GetParentId(row_cert) == 1975);
  CHECK(Chart229::GetDepth(row_cert) == 10);

  auto row_empty = Chart229::Parse("");
  CHECK(Chart229::GetId(row_empty) == -1);
  CHECK(Chart229::GetParentId(row_empty) == -1);
  CHECK(Chart229::GetDepth(row_empty) == 0);

  // Mixed whitespace (spaces and tabs) tokenization via cc-lib Util
  auto row_tab = Chart229::Parse("ce \t 7c9 \t\t 7b7 \t a \t 70d \t 1.4ef0d7e762624p-11 \t 7 \t d \t 1 \t 8 \t ");
  CHECK(std::holds_alternative<Chart229::CertRow>(row_tab));
  CHECK(std::get<Chart229::CertRow>(row_tab) == std::get<Chart229::CertRow>(row_cert));

  // Legacy serialization
  CHECK(Chart229::SerializeLegacy(row_cert) == "CE 1993 1975 10 1805 0.00063884886633153561 7 13 1 8");

  printf("  Comments and utilities tests PASSED.\n");
}

static void TestErrorHandling() {
  printf("Testing error handling on malformed lines...\n");

  // Unknown tag
  auto err1 = Chart229::Parse("UNKNOWN_TAG 1 2 3");
  CHECK(Chart229::IsError(err1));

  // Truncated row
  auto err2 = Chart229::Parse("ce 1 2");
  CHECK(Chart229::IsError(err2));

  // Invalid hex characters
  auto err3 = Chart229::Parse("ce 1 2 3 xyz 0.0 1 2 3");
  CHECK(Chart229::IsError(err3));

  // Extra trailing junk
  auto err4 = Chart229::Parse("sp 1 2 3 4 5 EXTRA_JUNK");
  CHECK(Chart229::IsError(err4));

  // Malformed float
  auto err5 = Chart229::Parse("tu 1 0 1 not_a_float");
  CHECK(Chart229::IsError(err5));

  printf("  Error handling tests PASSED.\n");
}

static void TestGeometryRow() {
  printf("Testing GeometryRow (ge and GE)...\n");

  // 1. Legacy decimal GE row
  // GE id parent_id depth box_depth view_depth chart cx cy cz rx ry rz v0x v0y v0z v1x v1y v1z v2x v2y v2z best_margin
  std::string legacy_str =
      "GE 500 200 12 8 4 1 "
      "0.125 -0.5 0.75 0.015625 0.03125 0.0625 "
      "1 0 0 0 1 0 0 0 1 "
      "0.001953125";
  auto ge_legacy = Chart229::Parse(legacy_str);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(ge_legacy));
  const auto &g1 = std::get<Chart229::GeometryRow>(ge_legacy);
  CHECK(g1.id == 500 && g1.parent_id == 200 && g1.depth == 12);
  CHECK(g1.box_depth == 8 && g1.view_depth == 4 && g1.chart == 1);
  CHECK(g1.cx == 0.125 && g1.cy == -0.5 && g1.cz == 0.75);
  CHECK(g1.rx == 0.015625 && g1.ry == 0.03125 && g1.rz == 0.0625);
  CHECK(g1.v0x == 1.0 && g1.v0y == 0.0 && g1.v0z == 0.0);
  CHECK(g1.v1x == 0.0 && g1.v1y == 1.0 && g1.v1z == 0.0);
  CHECK(g1.v2x == 0.0 && g1.v2y == 0.0 && g1.v2z == 1.0);
  CHECK(g1.best_margin == 0.001953125);
  CHECK(Chart229::GetId(ge_legacy) == 500);
  CHECK(Chart229::GetParentId(ge_legacy) == 200);
  CHECK(Chart229::GetDepth(ge_legacy) == 12);

  // 2. Compact hex ge serialization and round-trip
  std::string hex_str = Chart229::Serialize(g1);
  CHECK(hex_str.rfind("ge 1f4 c8 c 8 4 1 ", 0) == 0);
  auto ge_parsed = Chart229::Parse(hex_str);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(ge_parsed));
  const auto &g2 = std::get<Chart229::GeometryRow>(ge_parsed);
  CHECK(g2 == g1);

  // 3. Optional best_margin omitted
  std::string no_margin =
      "GE 10 5 3 2 1 0 "
      "0 0 0 1 1 1 "
      "1 0 0 0 1 0 0 0 1";
  auto ge_no_margin = Chart229::Parse(no_margin);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(ge_no_margin));
  const auto &g3 = std::get<Chart229::GeometryRow>(ge_no_margin);
  CHECK(g3.id == 10 && g3.best_margin == 0.0);

  // 4. Legacy decimal serialization round-trip
  std::string legacy_serialized = Chart229::SerializeLegacy(g1);
  auto ge_legacy_parsed = Chart229::Parse(legacy_serialized);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(ge_legacy_parsed));
  const auto &g4 = std::get<Chart229::GeometryRow>(ge_legacy_parsed);
  CHECK(g4 == g1);

  printf("  GeometryRow tests PASSED.\n");
}

static void TestLegacyDifficultParser() {
  printf("Testing Legacy .difficult file parsing...\n");

  // 1. Single untagged decimal line
  std::string line =
      "123 45 6 4 2 3 "
      "0.5 -0.25 0.125 0.01 0.02 0.03 "
      "1 0 0 0 1 0 0 0 1 "
      "0.005\n";
  auto row = Chart229::ParseLegacyDifficultLine(line);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(row));
  const auto &g = std::get<Chart229::GeometryRow>(row);
  CHECK(g.id == 123 && g.parent_id == 45 && g.depth == 6);
  CHECK(g.box_depth == 4 && g.view_depth == 2 && g.chart == 3);
  CHECK(g.cx == 0.5 && g.cy == -0.25 && g.cz == 0.125);
  CHECK(g.rx == 0.01 && g.ry == 0.02 && g.rz == 0.03);
  CHECK(g.best_margin == 0.005);

  // 2. Untagged line without best_margin
  std::string line2 =
      "124 45 6 4 2 3 "
      "0.5 -0.25 0.125 0.01 0.02 0.03 "
      "1 0 0 0 1 0 0 0 1";
  auto row2 = Chart229::ParseLegacyDifficultLine(line2);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(row2));
  const auto &g2 = std::get<Chart229::GeometryRow>(row2);
  CHECK(g2.id == 124 && g2.best_margin == 0.0);

  // 3. SerializeLegacyDifficult format check
  std::string difficult_out = Chart229::SerializeLegacyDifficult(g);
  auto re_parsed = Chart229::ParseLegacyDifficultLine(difficult_out);
  CHECK(std::holds_alternative<Chart229::GeometryRow>(re_parsed));
  CHECK(std::get<Chart229::GeometryRow>(re_parsed) == g);

  // 4. Multiline content with comments and blanks
  std::string file_content =
      "# id parent_id depth box_depth view_depth chart cx cy cz rx ry rz v0x v0y v0z v1x v1y v1z v2x v2y v2z best_margin\n"
      "\n"
      "123 45 6 4 2 3 0.5 -0.25 0.125 0.01 0.02 0.03 1 0 0 0 1 0 0 0 1 0.005\n"
      "# Another comment\n"
      "  \n"
      "ge 7b 2d 6 4 2 3 1p-1 -1p-2 1p-3 1.47ae147ae147bp-7 1.47ae147ae147bp-6 1.eb851eb851eb8p-6 1p0 0p+0 0p+0 0p+0 1p0 0p+0 0p+0 0p+0 1p0 1.47ae147ae147bp-8\n";

  std::string error;
  auto parsed_cells = Chart229::ParseLegacyDifficultContent(file_content, &error);
  CHECK(error.empty());
  CHECK(parsed_cells.size() == 2);
  CHECK(parsed_cells[0].id == 123);
  CHECK(parsed_cells[1].id == 123);  // 0x7b == 123

  printf("  Legacy .difficult file parsing tests PASSED.\n");
}

int main() {
  TestCertRow();
  TestMixedCertRow();
  TestSplitRows();
  TestPruneRows();
  TestTubeAndDifficultRows();
  TestGeometryRow();
  TestLegacyDifficultParser();
  TestCommentsAndUtilities();
  TestErrorHandling();

  printf("\nAll Chart229 tests PASSED successfully!\n");
  return 0;
}
