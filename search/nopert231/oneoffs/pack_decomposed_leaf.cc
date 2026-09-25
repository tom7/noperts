// pack_decomposed_leaf.cc: Packs a decomposed / annular certificate for
// triangle 031213002112122012121 into Lean 4 packed format (.pack).

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <cstdint>

static inline std::string ZigzagRat(int64_t num, int64_t den) {
  int64_t zz = (num >= 0) ? (num * 2) : ((-num) * 2 - 1);
  return std::to_string(zz) + "," + std::to_string(den);
}

struct ContactQ {
  int edge_start;
  int edge_finish;
  int edge_start2;
  int edge_finish2;
  int mix;
  int vertex;
};

struct AxisCertQ {
  ContactQ contacts[3];
  int nonzero_witness[3];
  int64_t B_num;
  int64_t B_den;
};

void WriteAxis(std::ostream &out, const AxisCertQ &ax) {
  for (int m = 0; m < 3; m++) out << "," << ax.contacts[m].edge_start;
  for (int m = 0; m < 3; m++) out << "," << ax.contacts[m].edge_finish;
  for (int m = 0; m < 3; m++) out << "," << ax.contacts[m].edge_start2;
  for (int m = 0; m < 3; m++) out << "," << ax.contacts[m].edge_finish2;
  for (int m = 0; m < 3; m++) out << "," << ax.contacts[m].mix;
  for (int m = 0; m < 3; m++) out << "," << ax.contacts[m].vertex;
  for (int m = 0; m < 3; m++) out << "," << ax.nonzero_witness[m];
  out << "," << ZigzagRat(ax.B_num, ax.B_den);
}

int main(int argc, char **argv) {
  std::string output_path = "ruperts/decomposed_leaf.pack";
  if (argc > 1) output_path = argv[1];

  // Path relative to root triangle "0"
  std::string path = "31213002112122012121";

  // Inner core cert on 9-vertex hull
  AxisCertQ cert_core = {
    {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {10, 15, 15, 19, 800, 15}
    },
    {9, 15, 1},
    18061, 10000
  };

  // Sibling axes 1, 2, 3
  AxisCertQ cert1 = {
    {
      {15, 19, 19, 3, 200, 19},
      {2, 1, 1, 4, 200, 1},
      {8, 9, 9, 10, 200, 9}
    },
    {8, 15, 2},
    898481993, 1000000000
  };

  AxisCertQ cert2 = {
    {
      {2, 1, 1, 4, 0, 1},
      {10, 15, 15, 19, 333, 15},
      {10, 15, 15, 19, 0, 15}
    },
    {15, 1, 4},
    254450361, 500000000
  };

  AxisCertQ cert3 = {
    {
      {3, 2, 2, 1, 800, 2},
      {4, 8, 8, 9, 800, 8},
      {14, 15, 15, 19, 800, 15}
    },
    {9, 19, 1},
    264825469, 200000000
  };

  std::ofstream out(output_path, std::ios::binary);
  if (!out.is_open()) {
    std::cerr << "Failed to open " << output_path << "\n";
    return 1;
  }

  // Header: 1 row, symmetryIndex = 0, table_r = 1/2000
  out << "1,0," << ZigzagRat(1, 2000);

  // Tag 2: Decomposed Certificate row
  // Format: tag(2), id(0), root(0), path_len, [path_digits], symmetryIndex(0),
  // r_min, r, c, delta, inner_indices(3), [inner_core_axis], num_complement(3), [cert1, cert2, cert3]
  out << ",2,0,0," << path.size();
  for (char ch : path) {
    out << "," << (ch - '0');
  }
  out << ",0"; // symmetryIndex = 0

  // r_min, r, c, delta
  out << "," << ZigzagRat(1, 10000);
  out << "," << ZigzagRat(1, 2000);
  out << "," << ZigzagRat(1, 1000);
  out << "," << ZigzagRat(1, 100000);

  // inner indices
  out << ",2,4,15";

  // inner core axis
  WriteAxis(out, cert_core);

  // num_complement = 3
  out << ",3";
  WriteAxis(out, cert1);
  WriteAxis(out, cert2);
  WriteAxis(out, cert3);

  out << "\n";
  out.close();

  std::cout << "Successfully packed decomposed certificate to " << output_path << "\n";
  return 0;
}
