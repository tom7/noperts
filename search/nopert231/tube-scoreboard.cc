#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <sys/stat.h>

#include "ansi.h"
#include "base/stringprintf.h"
#include "rapidjson/document.h"

#define SYM_VALID "⏺"
#define SYM_PACKED "◎"
#define SYM_CERT "○"
#define SYM_INCOMPLETE "•"

// Number of triangles for each code 0..78 from BDD polygon decomposition
static const int kCodeTriangles[79] = {
  2, 1, 1, 4, 2, 3, 1, 3, 1, 2,  //  0.. 9
  1, 1, 2, 3, 2, 1, 3, 1, 3, 4,  // 10..19
  1, 2, 1, 1, 5, 1, 1, 2, 2, 1,  // 20..29
  4, 2, 2, 2, 2, 1, 3, 3, 1, 3,  // 30..39
  2, 2, 1, 1, 3, 3, 2, 2, 2, 1,  // 40..49
  1, 4, 1, 3, 1, 1, 3, 3, 1, 3,  // 50..59
  1, 1, 5, 2, 1, 1, 1, 2, 3, 1,  // 60..69
  3, 1, 1, 2, 2, 3, 2, 2, 2      // 70..78
};

enum Status {
  STATUS_NO_DATA = 0,
  STATUS_CERTIFIED = 1,
  STATUS_PACKED = 2,
  STATUS_VALIDATED = 3,
};

static bool FileExists(const std::string &path) {
  struct stat st;
  return (stat(path.c_str(), &st) == 0 && st.st_size > 0);
}

static bool IsValidated(const std::string &val_path) {
  std::ifstream f(val_path);
  if (!f.is_open()) return false;
  std::string line;
  while (std::getline(f, line)) {
    if (line.find("table.Valid PROVED") != std::string::npos) return true;
  }
  return false;
}

static bool HasTreeCertificate(int code, int tri) {
  std::string tree_path = std::format("trees/tree.{}.json", code);
  std::ifstream f(tree_path);
  if (!f.is_open()) return false;

  std::stringstream ss;
  ss << f.rdbuf();
  std::string json_str = ss.str();

  rapidjson::Document doc;
  if (doc.Parse(json_str.c_str()).HasParseError()) return false;
  if (!doc.HasMember("triangles") || !doc["triangles"].IsArray()) return false;

  const auto &triangles = doc["triangles"];
  if (tri >= (int)triangles.Size()) return false;

  const auto &tri_obj = triangles[tri];
  if (tri_obj.HasMember("direct_bounds") && tri_obj["direct_bounds"].IsObject()) {
    const auto &db = tri_obj["direct_bounds"];
    if (db.HasMember("direct_r_lower") && db["direct_r_lower"].IsString()) {
      std::string r_str = db["direct_r_lower"].GetString();
      if (!r_str.empty() && r_str != "0" && r_str[0] != '-') return true;
    }
  }
  return false;
}

int main(int argc, char **argv) {
  std::string packs_dir = "/root/quad/Noperthedron/.artifacts/nopert229/packs";
  if (argc > 1) {
    packs_dir = argv[1];
  }

  // Evaluate status for each code and triangle
  Status matrix[79][5];
  int total_triangles = 0;
  int count_validated = 0;
  int count_packed = 0;
  int count_certified = 0;
  int count_no_data = 0;

  for (int c = 0; c < 79; c++) {
    int num_tri = kCodeTriangles[c];
    total_triangles += num_tri;
    for (int t = 0; t < 5; t++) {
      if (t >= num_tri) {
        matrix[c][t] = STATUS_NO_DATA;
        continue;
      }
      std::string val_path = std::format("{}/code_{}_tri_{}.pack.validated",
                                         packs_dir, c, t);
      std::string pack_path = std::format("{}/code_{}_tri_{}.pack",
                                          packs_dir, c, t);

      if (FileExists(val_path) && IsValidated(val_path)) {
        matrix[c][t] = STATUS_VALIDATED;
        count_validated++;
      } else if (FileExists(pack_path)) {
        matrix[c][t] = STATUS_PACKED;
        count_packed++;
      } else if (HasTreeCertificate(c, t)) {
        matrix[c][t] = STATUS_CERTIFIED;
        count_certified++;
      } else {
        matrix[c][t] = STATUS_NO_DATA;
        count_no_data++;
      }
    }
  }

  // Print Header
  std::cout << "\n" ANSI_WHITE
            << "========================================================================================\n"
            << "                NOPERT #229 IDENTITY TUBE COVERAGE SCOREBOARD (S²)\n"
            << "========================================================================================\n"
            << ANSI_RESET;

  // Print Legend
  std::cout
    << " Legend: "
    << ANSI_GREEN SYM_VALID ANSI_RESET " Validated (Lean 4 table.Valid)   "
    << ANSI_CYAN SYM_PACKED ANSI_RESET " Packed (.pack file ready)   "
    << ANSI_YELLOW SYM_CERT ANSI_RESET " Certified (tree r > 0)   "
    << ANSI_RED SYM_INCOMPLETE ANSI_RESET " Incomplete / No data\n"
    << "----------------------------------------------------------------------------------------\n\n";

  // Print 4-column matrix
  // Column 0: 00..19, Column 1: 20..39, Column 2: 40..59, Column 3: 60..78
  const int rows_per_col = 20;
  for (int r = 0; r < rows_per_col; r++) {
    for (int col = 0; col < 4; col++) {
      int c = col * rows_per_col + r;
      if (c >= 79) {
        std::cout << "                     ";
        continue;
      }
      int num_tri = kCodeTriangles[c];
      std::cout << ANSI_WHITE << "#" << std::setw(2) << std::setfill('0') << c << ANSI_RESET << " [";
      for (int t = 0; t < 5; t++) {
        if (t >= num_tri) {
          std::cout << " ";
        } else {
          switch (matrix[c][t]) {
            case STATUS_VALIDATED:
              std::cout << ANSI_GREEN SYM_VALID ANSI_RESET;
              break;
            case STATUS_PACKED:
              std::cout << ANSI_CYAN SYM_PACKED ANSI_RESET;
              break;
            case STATUS_CERTIFIED:
              std::cout << ANSI_YELLOW SYM_CERT ANSI_RESET;
              break;
            case STATUS_NO_DATA:
              std::cout << ANSI_RED SYM_INCOMPLETE ANSI_RESET;
              break;
          }
        }
      }
      std::cout << "]   ";
    }
    std::cout << "\n";
  }

  // Summary statistics
  int fully_validated_codes = 0;
  for (int c = 0; c < 79; c++) {
    bool all_val = true;
    for (int t = 0; t < kCodeTriangles[c]; t++) {
      if (matrix[c][t] != STATUS_VALIDATED) { all_val = false; break; }
    }
    if (all_val) fully_validated_codes++;
  }

  std::cout << "\n----------------------------------------------------------------------------------------\n";
  std::cout << ANSI_WHITE << " SUMMARY PROGRESS:" ANSI_RESET << "\n";
  std::cout << std::setfill(' ');
  std::cout << "   Total Spherical Codes:     79  ("
            << ANSI_GREEN << fully_validated_codes << " fully proved" ANSI_RESET << ", "
            << ANSI_YELLOW << (79 - fully_validated_codes) << " remaining" ANSI_RESET << ")\n";
  std::cout << "   Total Polygon Triangles:  157\n";
  std::cout << "     " ANSI_GREEN SYM_VALID ANSI_RESET " Validated in Lean 4:   "
            << std::setw(3) << count_validated << " / " << total_triangles
            << "  (" << std::fixed << std::setprecision(1) << (100.0 * count_validated / total_triangles) << "%)\n";
  std::cout << "     " ANSI_CYAN SYM_PACKED ANSI_RESET " Packed for Lean:       "
            << std::setw(3) << count_packed << " / " << total_triangles
            << "  (" << std::fixed << std::setprecision(1) << (100.0 * count_packed / total_triangles) << "%)\n";
  std::cout << "     " ANSI_YELLOW SYM_CERT ANSI_RESET " Certified in Trees:    "
            << std::setw(3) << count_certified << " / " << total_triangles
            << "  (" << std::fixed << std::setprecision(1) << (100.0 * count_certified / total_triangles) << "%)\n";
  std::cout << "     " ANSI_RED SYM_INCOMPLETE ANSI_RESET " Incomplete / Solving:  "
            << std::setw(3) << count_no_data << " / " << total_triangles
            << "  (" << std::fixed << std::setprecision(1) << (100.0 * count_no_data / total_triangles) << "%)\n";

  // List remaining incomplete or non-validated triangles
  if (count_validated < total_triangles) {
    std::cout << "\n" ANSI_WHITE << " REMAINING TRIANGLES TO FINISH:" ANSI_RESET << "\n";
    for (int c = 0; c < 79; c++) {
      for (int t = 0; t < kCodeTriangles[c]; t++) {
        if (matrix[c][t] != STATUS_VALIDATED) {
          std::cout << "   Code " << std::setw(2) << c << " Tri " << t << ": ";
          if (matrix[c][t] == STATUS_PACKED) {
            std::cout << ANSI_CYAN SYM_PACKED " PACKED" ANSI_RESET << " (ready for validate_code_pack)\n";
          } else if (matrix[c][t] == STATUS_CERTIFIED) {
            std::cout << ANSI_YELLOW SYM_CERT " CERTIFIED" ANSI_RESET << " (ready for export_codetrees_pack)\n";
          } else {
            std::cout << ANSI_RED SYM_INCOMPLETE " INCOMPLETE" ANSI_RESET;
            std::cout << "\n";
          }
        }
      }
    }
  }

  std::cout << "========================================================================================\n\n";
  return 0;
}
