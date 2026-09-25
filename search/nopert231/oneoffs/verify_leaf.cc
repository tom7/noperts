#define PACK229_NO_MAIN
#include "pack229.cc"

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <string>

int main(int argc, char **argv) {
  int64_t target_leaf_id = 12651740069024;
  if (argc > 1) {
    target_leaf_id = std::stoll(argv[1]);
  }
  std::cout << "Verifying multi-vertex certificate for leaf node " << target_leaf_id << "...\n";

  // Difficult cell 12651740069 parameters from chart0.difficult:
  // center = (1/2048, -1/2048, -1/1024)
  // radii = (1/2048, 1/2048, 1/3072)
  // triangle corners with denominator 83968:
  // T0 = (52427/83968, 11532/83968, 20009/83968)
  // T1 = (52468/83968, 11532/83968, 19968/83968)
  // T2 = (52437/83968, 11563/83968, 19968/83968)

  CayleyBoxQ root_box;
  root_box.center = Vec3Q(BigRat(1, 2048), BigRat(-1, 2048), BigRat(-1, 1024));
  root_box.radii = Vec3Q(BigRat(1, 2048), BigRat(1, 2048), BigRat(1, 3072));

  TriangleQ root_tri;
  root_tri.corners[0] = Vec3Q(BigRat(52427, 83968), BigRat(11532, 83968), BigRat(20009, 83968));
  root_tri.corners[1] = Vec3Q(BigRat(52468, 83968), BigRat(11532, 83968), BigRat(19968, 83968));
  root_tri.corners[2] = Vec3Q(BigRat(52437, 83968), BigRat(11563, 83968), BigRat(19968, 83968));

  // Load done file
  std::string done_file = "/root/tom7misc/ruperts/chart0.12651740069.done.tmp";
  std::ifstream infile(done_file);
  if (!infile.is_open()) {
    std::cerr << "Cannot open " << done_file << "\n";
    return 1;
  }

  std::unordered_map<int64_t, ParsedNode> nodes_map;
  std::unordered_map<int64_t, StoredMixedCert> mixed_certs;
  std::string line;
  int64_t cert_delta = 0;
  while (std::getline(infile, line)) {
    if (line.empty()) continue;
    ParsedNode pn;
    if (ParseRow(line, &pn, &mixed_certs, &cert_delta)) {
      nodes_map[pn.id] = pn;
    }
  }
  std::cout << "Loaded " << nodes_map.size() << " nodes from done file.\n";

  if (nodes_map.find(target_leaf_id) == nodes_map.end()) {
    std::cerr << "Leaf " << target_leaf_id << " not found in done file!\n";
    return 1;
  }

  // Find ancestry path from root (12651740069) to target_leaf_id
  std::vector<int64_t> path;
  int64_t curr = target_leaf_id;
  while (curr != 12651740069 && curr != -1) {
    path.push_back(curr);
    auto it = nodes_map.find(curr);
    if (it == nodes_map.end()) {
      std::cerr << "Node " << curr << " not found!\n";
      return 1;
    }
    curr = it->second.parent_id;
  }
  path.push_back(12651740069);
  std::reverse(path.begin(), path.end());

  std::cout << "Ancestry path length: " << path.size() << "\n";
  for (size_t i = 0; i < path.size(); i++) {
    std::cout << "  step " << i << ": node " << path[i] << " (tag " << (int)nodes_map[path[i]].tag << ")\n";
  }

  // Follow the path to reconstruct CayleyBoxQ and TriangleQ
  CayleyBoxQ curr_box = root_box;
  TriangleQ curr_tri = root_tri;

  for (size_t i = 0; i + 1 < path.size(); i++) {
    int64_t p_id = path[i];
    int64_t c_id = path[i + 1];
    const auto &p_node = nodes_map[p_id];

    if (p_node.tag == NodeTag::SPLIT || p_node.tag == NodeTag::SPLIT_ORIGIN) {
      int axis = curr_box.WidestAxis();
      if (c_id == p_node.child_ids[0]) {
        // lower child
        if (axis == 0) {
          curr_box.radii.x = curr_box.radii.x / BigRat(2);
          curr_box.center.x = curr_box.center.x - curr_box.radii.x;
        } else if (axis == 1) {
          curr_box.radii.y = curr_box.radii.y / BigRat(2);
          curr_box.center.y = curr_box.center.y - curr_box.radii.y;
        } else {
          curr_box.radii.z = curr_box.radii.z / BigRat(2);
          curr_box.center.z = curr_box.center.z - curr_box.radii.z;
        }
      } else if (c_id == p_node.child_ids[1]) {
        // upper child
        if (axis == 0) {
          curr_box.radii.x = curr_box.radii.x / BigRat(2);
          curr_box.center.x = curr_box.center.x + curr_box.radii.x;
        } else if (axis == 1) {
          curr_box.radii.y = curr_box.radii.y / BigRat(2);
          curr_box.center.y = curr_box.center.y + curr_box.radii.y;
        } else {
          curr_box.radii.z = curr_box.radii.z / BigRat(2);
          curr_box.center.z = curr_box.center.z + curr_box.radii.z;
        }
      } else {
        std::cerr << "Child ID " << c_id << " not found in parent " << p_id << " children!\n";
        return 1;
      }
    } else if (p_node.tag == NodeTag::SPLIT_VIEW) {
      auto sub_tris = curr_tri.Subdivide();
      int match_idx = -1;
      for (int t = 0; t < 4; t++) {
        if (p_node.child_ids[t] == c_id) {
          match_idx = t;
          break;
        }
      }
      if (match_idx == -1) {
        std::cerr << "Child ID " << c_id << " not found in SV parent " << p_id << " children!\n";
        return 1;
      }
      curr_tri = sub_tris[match_idx];
    }
  }

  std::cout << "\nReconstructed CayleyBoxQ for leaf:\n";
  std::cout << "  center: (" << curr_box.center.x.ToString() << ", "
            << curr_box.center.y.ToString() << ", "
            << curr_box.center.z.ToString() << ")\n";
  std::cout << "  radii:  (" << curr_box.radii.x.ToString() << ", "
            << curr_box.radii.y.ToString() << ", "
            << curr_box.radii.z.ToString() << ")\n";

  std::cout << "\nReconstructed TriangleQ for leaf:\n";
  for (int c = 0; c < 3; c++) {
    std::cout << "  C" << c << ": (" << curr_tri.corners[c].x.ToString() << ", "
              << curr_tri.corners[c].y.ToString() << ", "
              << curr_tri.corners[c].z.ToString() << ")\n";
  }

  // Now verify with ComputeExactComponent using candidate samples
  const auto &leaf_node = nodes_map[target_leaf_id];
  std::cout << "\nLeaf node details:\n";
  std::cout << "  tag: " << (int)leaf_node.tag << " (CERT=" << (int)NodeTag::CERT << ")\n";
  std::cout << "  winning_triple: " << leaf_node.winning_triple << "\n";
  std::cout << "  inner vertices: " << leaf_node.inner[0] << ", "
            << leaf_node.inner[1] << ", " << leaf_node.inner[2] << "\n";

  vec3 tri_d[3] = {curr_tri.corners[0].ToVec3D(), curr_tri.corners[1].ToVec3D(), curr_tri.corners[2].ToVec3D()};

  std::vector<int> candidate_samples = {8, 12, 16, 24, 32};
  bool verified = false;
  AxisCertificateQ cert_q;
  BigRat ball_multiplier(0);
  int inner_out[3] = {-1, -1, -1};

  for (int s : candidate_samples) {
    auto pool = BuildTrianglePool(tri_d, s, /*sort_triples=*/false);
    const auto &triple = pool->gpu_triples[leaf_node.winning_triple];
    std::cout << "  cone sample " << s << ": triple.weighted_defect_upper = " << triple.weighted_defect_upper << "\n";
    if (ComputeExactComponent(curr_tri, curr_box, leaf_node.winning_triple,
                               leaf_node.inner, inner_out, pool,
                               &cert_q, &ball_multiplier, target_leaf_id,
                               /*verbose=*/true, /*check_displacement=*/true)) {
      verified = true;
      std::cout << "\n" << ANSI_GREEN << "SUCCESS: ComputeExactComponent verified leaf!" << ANSI_RESET
                << " (using cone sample pool " << s << ")\n";
      break;
    }
  }

  if (!verified) {
    std::cerr << ANSI_RED << "FAILED: ComputeExactComponent did not verify leaf." << ANSI_RESET << "\n";
    return 1;
  }

  std::cout << "\nVerified Exact Certificate:\n";
  std::cout << "  B: " << cert_q.B.ToString() << "\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  axis " << i << ": edgeStart=" << cert_q.edge_start[i]
              << " (" << cert_q.edge_finish[i] << ") - edgeStart2=" << cert_q.edge_start2[i]
              << " (" << cert_q.edge_finish2[i] << ") mix=" << cert_q.mix[i]
              << " witness=" << cert_q.nonzero_witness[i] << "\n";
  }
  std::cout << "  ball_multiplier: " << ball_multiplier.ToString() << "\n";

  // Now generate Lean 4 test file
  std::string lean_path = "/root/nopert-project/Noperthedron/VerifyLeafCert.lean";
  std::ofstream out(lean_path);
  out << "import Noperthedron.Nopert229.AtlasProjectiveGlobalCertificate\n\n";
  out << "open Noperthedron.Nopert229\n";
  out << "open Noperthedron.SnubCube.ProjectiveView\n";
  out << "open AtlasProjectiveGlobalCertificate\n";
  out << "open AtlasProjectiveLocalCertificate\n\n";

  auto to_lean_rat = [](const BigRat &q) -> std::string {
    BigInt num = q.Numerator();
    BigInt den = q.Denominator();
    if (den == BigInt(1)) return num.ToString();
    return "(" + num.ToString() + " : ℚ) / " + den.ToString();
  };

  out << "def testBoxInterval : AtlasInterval ℚ :=\n";
  out << "  AtlasInterval.mk\n";
  out << "    { θ := 0, φ := 0,\n";
  out << "      x := " << to_lean_rat(curr_box.center.x - curr_box.radii.x) << ",\n";
  out << "      y := " << to_lean_rat(curr_box.center.y - curr_box.radii.y) << ",\n";
  out << "      z := " << to_lean_rat(curr_box.center.z - curr_box.radii.z) << " }\n";
  out << "    { θ := 0, φ := 0,\n";
  out << "      x := " << to_lean_rat(curr_box.center.x + curr_box.radii.x) << ",\n";
  out << "      y := " << to_lean_rat(curr_box.center.y + curr_box.radii.y) << ",\n";
  out << "      z := " << to_lean_rat(curr_box.center.z + curr_box.radii.z) << " }\n";
  out << "    (by rw [AtlasPose.le_iff]; norm_num)\n\n";

  out << "def testTriangle : AtlasProjectiveView.Triangle ℚ := ![\n";
  for (int c = 0; c < 3; c++) {
    out << "  ![" << to_lean_rat(curr_tri.corners[c].x) << ", "
        << to_lean_rat(curr_tri.corners[c].y) << ", "
        << to_lean_rat(curr_tri.corners[c].z) << "]" << (c < 2 ? "," : "") << "\n";
  }
  out << "]\n\n";

  out << "def testCertificate : AxisCertificate where\n";
  out << "  edgeStart := ![" << cert_q.edge_start[0] << ", " << cert_q.edge_start[1] << ", " << cert_q.edge_start[2] << "]\n";
  out << "  edgeFinish := ![" << cert_q.edge_finish[0] << ", " << cert_q.edge_finish[1] << ", " << cert_q.edge_finish[2] << "]\n";
  out << "  edgeStart₂ := ![" << cert_q.edge_start2[0] << ", " << cert_q.edge_start2[1] << ", " << cert_q.edge_start2[2] << "]\n";
  out << "  edgeFinish₂ := ![" << cert_q.edge_finish2[0] << ", " << cert_q.edge_finish2[1] << ", " << cert_q.edge_finish2[2] << "]\n";
  out << "  mix := ![" << cert_q.mix[0] << ", " << cert_q.mix[1] << ", " << cert_q.mix[2] << "]\n";
  out << "  index := ![" << cert_q.support_index[0] << ", " << cert_q.support_index[1] << ", " << cert_q.support_index[2] << "]\n";
  out << "  nonzeroWitness := ![" << cert_q.nonzero_witness[0] << ", " << cert_q.nonzero_witness[1] << ", " << cert_q.nonzero_witness[2] << "]\n";
  out << "  B := " << to_lean_rat(cert_q.B) << "\n\n";

  out << "def testBox : AtlasProjectiveGlobalCertificate.Box where\n";
  out << "  interval := testBoxInterval\n";
  out << "  root := 0\n";
  out << "  triangle := testTriangle\n";
  out << "  chart := 0\n";
  out << "  certificate := testCertificate\n";
  out << "  innerIndex := ![" << inner_out[0] << ", " << inner_out[1] << ", " << inner_out[2] << "]\n";
  out << "  ballMultiplier := " << to_lean_rat(ball_multiplier) << "\n\n";

  out << "theorem test_triangle_valid :\n";
  out << "    AtlasProjectiveEdgeCertificate.SignedTriangleValid testBox.root testBox.triangle := by\n";
  out << "  native_decide\n\n";

  out << "theorem test_weights_valid :\n";
  out << "    (∀ i, 0 ≤ testBox.weightLower i) ∧ (∃ i, 0 < testBox.weightLower i) := by\n";
  out << "  native_decide\n\n";

  out << "theorem test_directions_valid :\n";
  out << "    ∀ i, testBox.supportUpper i (testBox.certificate.nonzeroWitness i) < 0 := by\n";
  out << "  native_decide\n\n";

  out << "theorem test_displacement_valid :\n";
  out << "    testBox.displacementError ≤\n";
  out << "      testBox.certifiedDisplacementLower - testBox.dBound * testBox.weightedDefectUpper := by\n";
  out << "  native_decide\n\n";

  out << "theorem test_box_valid_native : testBox.Valid := by\n";
  out << "  native_decide\n\n";

  out << "theorem test_box_valid_kernel : testBox.Valid := by\n";
  out << "  decide +kernel\n\n";



  out.close();
  std::cout << "\nGenerated Lean verification file: " << lean_path << "\n";

  return 0;
}
