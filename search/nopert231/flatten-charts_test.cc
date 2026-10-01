// flatten-charts_test.cc: Tests for geometry tracking and subchart absorption.

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include "chart229.h"
#include "flatten-charts.h"
#include "lib229.h"

#ifdef CHECK
#undef CHECK
#endif
#define CHECK(expr)                                                        \
  do {                                                                     \
    if (!(expr)) {                                                         \
      fprintf(stderr, "FAILED at %s:%d: %s\n", __FILE__, __LINE__, #expr); \
      abort();                                                             \
      }                                                                      \
  } while (0)

using namespace flatten_charts;

static void TestGeometryTracing() {
  printf("Testing geometry tracing through box and view splits...\n");

  NodeGeometry root = DefaultRootGeometry(0);
  CHECK(root.chart == 0);
  CHECK(root.box.radii.x == 1.0);
  CHECK(root.box.radii.y == 1.0);
  CHECK(std::abs(root.box.radii.z - 1.0 / 3.0) < 1e-9);

  std::unordered_map<int64_t, SplitRecord> splits;

  // Split root (id 0) along box -> children 1, 2
  splits[0] = SplitRecord{
      .parent_id = -1,
      .type = SplitType::BOX,
      .children = {1, 2},
  };

  // Split child 2 along view -> children 3, 4, 5, 6
  splits[2] = SplitRecord{
      .parent_id = 0,
      .type = SplitType::VIEW,
      .children = {3, 4, 5, 6},
  };

  // Split child 5 along box -> children 7, 8
  splits[5] = SplitRecord{
      .parent_id = 2,
      .type = SplitType::BOX,
      .children = {7, 8},
  };

  // Trace geometry for leaf node 8 (child 1 of node 5)
  auto geom_opt = TraceGeometry(8, 5, root, splits);
  CHECK(geom_opt.has_value());
  NodeGeometry g8 = *geom_opt;

  CHECK(g8.id == 8);
  CHECK(g8.parent_id == 5);
  CHECK(g8.depth == 3);
  CHECK(g8.box_depth == 2);
  CHECK(g8.view_depth == 1);
  CHECK(g8.chart == 0);

  // Manual trace:
  // Root: axis is 0 (X: 1.0, Y: 1.0; 0 is widest).
  // Split 0: child 2 is right (+), so center.x = 0.5, radius.x = 0.5.
  // View split on 2: child 5 is index 2 -> corner 2 subdivision.
  // Box split on 5: radii are X=0.5, Y=1.0, Z=1/3. Widest is Y (axis 1)!
  // Child 8 is index 1 (right +), so center.y = 0.5, radius.y = 0.5.
  CHECK(std::abs(g8.box.center.x - 0.5) < 1e-9);
  CHECK(std::abs(g8.box.radii.x - 0.5) < 1e-9);
  CHECK(std::abs(g8.box.center.y - 0.5) < 1e-9);
  CHECK(std::abs(g8.box.radii.y - 0.5) < 1e-9);

  printf("Geometry tracing verified successfully.\n");
}

static void TestSmallFileAbsorption() {
  printf("Testing absorption of <= threshold .subchart files...\n");

  std::string test_dir = "./test_scratch_flatten";
  std::filesystem::create_directories(test_dir);

  // Create parent chart with a split and a df row
  std::string parent_path = test_dir + "/chart0.parent.subchart";
  {
    std::ofstream out(parent_path);
    out << "ge 1 -1 0 0 0 0 0 0 0 1 1 0.5555555555555556 1 0 0 0.24390243902439024 0.7560975609756098 0 0 0 1\n";
    out << "sp 1 -1 0 2 3\n";
    out << "ce 2 1 1 12 1.5p-10 1 2 3 8\n";
    out << "df 3 1 1\n";
  }

  // Create a small .subchart file for node 3: 3 rows (<= threshold 5)
  std::string child_path = test_dir + "/chart0.3.subchart";
  {
    std::ofstream out(child_path);
    out << "ge 3 1 1 1 0 0 0.5 0 0 0.5 1 0.5555555555555556 1 0 0 0.24390243902439024 0.7560975609756098 0 0 0 1\n";
    out << "sp 3 1 1 4 5\n";
    out << "ce 4 3 2 15 1.2p-12 1 2 4 8\n";
    out << "ce 5 3 2 18 1.4p-12 1 2 5 8\n";
  }

  FlattenOptions options;
  options.subcharts_dir = test_dir;
  options.threshold = 5;
  options.dry_run = false;
  options.keep_subcharts = false;

  FlattenStats stats;
  bool ok = FlattenChartFile(parent_path, parent_path, options, stats, 0);
  CHECK(ok);
  CHECK(stats.df_rows_found == 1);
  CHECK(stats.files_absorbed == 1);
  CHECK(stats.rows_absorbed == 3);
  CHECK(stats.subcharts_removed == 1);

  // Verify that child .subchart was removed
  CHECK(!std::filesystem::exists(child_path));

  // Verify parent content
  std::ifstream in(parent_path);
  std::string line;
  std::vector<std::string> lines;
  while (std::getline(in, line)) {
    if (!line.empty()) lines.push_back(line);
  }

  // Expect: ge, sp 1, ce 2, sp 3, ce 4', ce 5' (with 4 and 5 remapped)
  CHECK(lines.size() == 6);
  CHECK(lines[0].rfind("ge 1", 0) == 0);
  CHECK(lines[1].rfind("sp 1", 0) == 0);
  CHECK(lines[2].rfind("ce 2", 0) == 0);
  CHECK(lines[3].rfind("sp 3", 0) == 0);
  CHECK(lines[4].rfind("ce ", 0) == 0);
  CHECK(lines[5].rfind("ce ", 0) == 0);

  std::filesystem::remove_all(test_dir);
  printf("Small file absorption verified successfully.\n");
}

static void TestLargeFileRetention() {
  printf("Testing retention of > threshold .subchart files...\n");

  std::string test_dir = "./test_scratch_flatten_large";
  std::filesystem::create_directories(test_dir);

  std::string parent_path = test_dir + "/chart0.parent.subchart";
  {
    std::ofstream out(parent_path);
    out << "ge 1 -1 0 0 0 0 0 0 0 1 1 0.5555555555555556 1 0 0 0.24390243902439024 0.7560975609756098 0 0 0 1\n";
    out << "sp 1 -1 0 2 3\n";
    out << "ce 2 1 1 12 1.5p-10 1 2 3 8\n";
    out << "df 3 1 1\n";
  }

  // Create a .subchart file for node 3 with 5 rows (> threshold 4)
  std::string child_path = test_dir + "/chart0.3.subchart";
  {
    std::ofstream out(child_path);
    out << "ge 3 1 1 1 0 0 0.5 0 0 0.5 1 0.5555555555555556 1 0 0 0.24390243902439024 0.7560975609756098 0 0 0 1\n";
    out << "sp 3 1 1 4 5\n";
    out << "sp 4 3 2 6 7\n";
    out << "ce 5 3 2 18 1.4p-12 1 2 5 8\n";
    out << "ce 6 4 3 20 1.1p-12 1 2 6 8\n";
    out << "ce 7 4 3 22 1.3p-12 1 2 7 8\n";
  }

  FlattenOptions options;
  options.subcharts_dir = test_dir;
  options.threshold = 4;  // threshold is 4, file has 5 rows
  options.dry_run = false;
  options.keep_subcharts = false;

  FlattenStats stats;
  bool ok = FlattenChartFile(parent_path, parent_path, options, stats, 0);
  CHECK(ok);
  CHECK(stats.df_rows_found == 1);
  CHECK(stats.files_absorbed == 0);
  CHECK(stats.subcharts_removed == 0);

  // Large subchart retained
  CHECK(std::filesystem::exists(child_path));

  // Parent should STILL contain df 3
  std::ifstream p_in(parent_path);
  std::string p_line;
  bool found_df = false;
  while (std::getline(p_in, p_line)) {
    if (p_line.rfind("df 3", 0) == 0) found_df = true;
  }
  CHECK(found_df);

  std::filesystem::remove_all(test_dir);
  printf("Large file retention verified successfully.\n");
}

int main() {
  TestGeometryTracing();
  TestSmallFileAbsorption();
  TestLargeFileRetention();
  printf("All flatten-charts tests passed!\n");
  return 0;
}
