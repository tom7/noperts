#include "base/print.h"
#include "geom/polyhedra.h"
#include "lib229.h"

#include "ansi.h"
#include "ruperts-util.h"
#include "solutions.h"
#include "yocto-math.h"
#include <format>
#include <string_view>

void TestKnownSolution() {
  Print(AYELLOW("Testing Rupert solution detection on known solution 1662...\n"));

  auto o_frame = SolutionDB::StringFrame(
      "-0.49746192508304149,0.72491410864775851,-0.47647787795038249,"
      "0.077349272600657409,0.58414142401727587,0.80795784962782424,"
      "0.86403051052658031,0.36507304999204515,-0.34665969631424132,0,0,0");
  auto i_frame = SolutionDB::StringFrame(
      "-0.49713703400231984,0.72470320344367012,-0.4771373348857319,"
      "0.076797862455929219,0.58449836059071414,0.80775228553620826,"
      "0.86426665893436894,0.36492044802292239,-0.34623143830272424,"
      "6.2363539751420424e-05,-4.037091880670955e-05,0");

  CHECK(o_frame && i_frame) << "Failed to parse frames!";

  Polyhedron poly = GetPolyhedron229();
  auto initial_c = GetClearance(poly, *o_frame, *i_frame);
  Print("Direct GetClearance on frames: {}\n",
        initial_c ? std::format("SUCCESS ({:.17g})", *initial_c) : "FAILED");

  // View direction is outer_frame column 2 in world coordinates mapped to poly space:
  vec3 sol_view = {o_frame->x.z, o_frame->y.z, o_frame->z.z};
  sol_view = yocto::normalize(sol_view);

  // Relative rotation R = R_outer^T * R_inner
  double R[3][3];
  vec3 out_cols[3] = {o_frame->x, o_frame->y, o_frame->z};
  vec3 inn_cols[3] = {i_frame->x, i_frame->y, i_frame->z};
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      R[i][j] = yocto::dot(out_cols[i], inn_cols[j]);
    }
  }
  double tr = R[0][0] + R[1][1] + R[2][2];
  double denom = 1.0 + tr;
  vec3 sol_w = {
    (R[2][1] - R[1][2]) / denom,
    (R[0][2] - R[2][0]) / denom,
    (R[1][0] - R[0][1]) / denom
  };

  Print("Extracted Cayley w: ({:.17g}, {:.17g}, {:.17g})\n",
        sol_w.x, sol_w.y, sol_w.z);
  Print("Extracted View v:  ({:.17g}, {:.17g}, {:.17g})\n",
        sol_view.x, sol_view.y, sol_view.z);

  // Test 1: Exact box centered at solution
  SearchNode node1;
  node1.id = 1;
  node1.depth = 64;
  node1.chart = 0;
  node1.box.center = sol_w;
  node1.box.radii = {1e-6, 1e-6, 1e-6};

  vec3 p0 = sol_view + vec3{1e-5, 0.0, 0.0};
  vec3 p1 = sol_view + vec3{-0.5e-5, 0.866e-5, 0.0};
  vec3 p2 = sol_view + vec3{-0.5e-5, -0.866e-5, 0.0};
  node1.tri.corners[0] = yocto::normalize(p0);
  node1.tri.corners[1] = yocto::normalize(p1);
  node1.tri.corners[2] = yocto::normalize(p2);

  Print("\n--- Case 1: Box centered at solution ---\n");
  auto witness1 = CheckSolutionWitness(node1);
  if (witness1) {
    Print(AGREEN("Case 1 PASSED: Verified clearance {:.17g}\n"),
          witness1->clearance);
  } else {
    Print(ARED("Case 1 FAILED!\n"));
  }

  // Test 2: Offset box where solution is in the interior, NOT at the center
  SearchNode node2 = node1;
  node2.id = 2;
  node2.box.center = sol_w + vec3{2.5e-7, -3.0e-7, 1.8e-7};
  node2.box.radii = {1e-6, 1e-6, 1e-6};

  Print("\n--- Case 2: Offset box (solution is interior, not at center) ---\n");
  auto witness2 = CheckSolutionWitness(node2);
  if (witness2) {
    Print(AGREEN("Case 2 PASSED: Verified clearance {:.17g}\n"
                 "Outer Frame:\n{}\n"
                 "Inner Frame:\n{}\n"),
          witness2->clearance,
          SolutionDB::FrameString(witness2->outer_frame),
          SolutionDB::FrameString(witness2->inner_frame));
  } else {
    Print(ARED("Case 2 FAILED!\n"));
  }

  Print("\n--- Part 3: Live tree-search subdivision test from depth 60 to max_depth 64 ---\n");
  SearchManager mgr;
  SearchNode ancestor;
  ancestor.id = mgr.next_node_id++;
  ancestor.parent_id = -1;
  ancestor.depth = 60;
  ancestor.box_depth = 48;
  ancestor.view_depth = 12;
  ancestor.chart = 0;
  ancestor.box.center = sol_w;
  ancestor.box.radii = {1e-5, 1e-5, 1e-5};
  ancestor.tri = node1.tri;

  mgr.stack.clear();
  mgr.stack.push_back(ancestor);
  mgr.max_depth = 64;
  mgr.batch_size = 64;
  mgr.resume = false;
  mgr.output_dir = ".artifacts/test_solution";
  mgr.Run();
}

void TestValleyPoint() {
  Print(AYELLOW("Testing valley hard points directly...\n"));
  for (int test_idx = 0; test_idx < 3; test_idx++) {
    vec3 sol_w = (test_idx == 0)
        ? vec3{0.00030419230461120605, -0.00036638975143432617, -0.0005896488825480144}
        : (test_idx == 1)
        ? vec3{0.0003413856029510498, -0.00041025876998901367, -0.00066292285919189442}
        : vec3{0.00041022896766662598, -0.00049299001693725586, -0.0007966756820678712};
    vec3 sol_view = yocto::normalize(vec3{0.9164627443138856, 0.2030404322634455, 0.3443121541818299});

    Print("Testing point {}: w=({:.8g}, {:.8g}, {:.8g})\n", test_idx, sol_w.x, sol_w.y, sol_w.z);

    SearchManager mgr;
    SearchNode ancestor;
    ancestor.id = mgr.next_node_id++;
    ancestor.parent_id = -1;
    ancestor.depth = 80;
    ancestor.box_depth = 64;
    ancestor.view_depth = 16;
    ancestor.chart = 0;
    ancestor.box.center = sol_w;
    ancestor.box.radii = {1e-6, 1e-6, 1e-6};

    vec3 p0 = sol_view + vec3{1e-5, 0.0, 0.0};
    vec3 p1 = sol_view + vec3{-0.5e-5, 0.866e-5, 0.0};
    vec3 p2 = sol_view + vec3{-0.5e-5, -0.866e-5, 0.0};
    ancestor.tri.corners[0] = yocto::normalize(p0);
    ancestor.tri.corners[1] = yocto::normalize(p1);
    ancestor.tri.corners[2] = yocto::normalize(p2);

    mgr.stack.clear();
    mgr.stack.push_back(ancestor);
    mgr.max_depth = 96;
    mgr.max_box_depth = 72;
    mgr.max_view_depth = 24;
    mgr.batch_size = 64;
    mgr.resume = false;
    mgr.output_dir = ".artifacts/test_valley";
    mgr.Run();
  }
}

void TestDepthOut() {
  Print(AYELLOW("Testing depth-out leaf directly with EvaluateBoxCPU...\n"));
  vec3 sol_w = {0.0003413856029510498, -0.00041025876998901367, -0.00066292285919189442};
  vec3 sol_r = {2.9802322387695312e-08, 5.9604644775390625e-08, 3.9736429850260414e-08};

  SearchNode node;
  node.id = 0;
  node.parent_id = -1;
  node.depth = 96;
  node.box_depth = 72;
  node.view_depth = 24;
  node.chart = 0;
  node.box.center = sol_w;
  node.box.radii = sol_r;
  node.tri.corners[0] = {0.6255792583, 0.1381680762, 0.2362526655};
  node.tri.corners[1] = {0.6255792881, 0.1381680762, 0.2362526357};
  node.tri.corners[2] = {0.6255792656, 0.1381680987, 0.2362526357};

  auto tpool = GetTrianglePool(node.tri, 14);
  GpuBox gbox;
  gbox.cx = node.box.center.x; gbox.cy = node.box.center.y; gbox.cz = node.box.center.z;
  gbox.rx = node.box.radii.x;  gbox.ry = node.box.radii.y;  gbox.rz = node.box.radii.z;
  for (int c = 0; c < 3; c++) {
    gbox.tri[c][0] = node.tri.corners[c].x;
    gbox.tri[c][1] = node.tri.corners[c].y;
    gbox.tri[c][2] = node.tri.corners[c].z;
  }
  gbox.chart = node.chart;
  gbox.triple_offset = 0;
  gbox.num_triples = tpool->gpu_triples.size();
  gbox.contact_offset = 0;
  gbox.num_contacts = tpool->contacts.size();
  gbox._pad = 0;
  auto res = EvaluateBoxCPU(gbox, tpool->contacts, tpool->gpu_triples);
  Print("At depth 96 (box_depth 72, view_depth 24): certified={}, winning_triple={}, margin={:.17g}\n",
        res.certified, res.winning_triple, res.margin);

  // Now test both halves of the bisected box (box_depth 73)
  GpuBox gbox0 = gbox;
  gbox0.cy = node.box.center.y - node.box.radii.y * 0.5;
  gbox0.ry = node.box.radii.y * 0.5;
  auto res0 = EvaluateBoxCPU(gbox0, tpool->contacts, tpool->gpu_triples);

  GpuBox gbox1 = gbox;
  gbox1.cy = node.box.center.y + node.box.radii.y * 0.5;
  gbox1.ry = node.box.radii.y * 0.5;
  auto res1 = EvaluateBoxCPU(gbox1, tpool->contacts, tpool->gpu_triples);

  Print("Child 0 (box_depth 73): certified={}, winning_triple={}, margin={:.17g}\n",
        res0.certified, res0.winning_triple, res0.margin);
  Print("Child 1 (box_depth 73): certified={}, winning_triple={}, margin={:.17g}\n",
        res1.certified, res1.winning_triple, res1.margin);

  // Bisect Child 1's widest remaining axis (rx or rz)
  GpuBox gbox10 = gbox1;
  gbox10.cz = gbox1.cz - gbox1.rz * 0.5;
  gbox10.rz = gbox1.rz * 0.5;
  auto res10 = EvaluateBoxCPU(gbox10, tpool->contacts, tpool->gpu_triples);

  GpuBox gbox11 = gbox1;
  gbox11.cz = gbox1.cz + gbox1.rz * 0.5;
  gbox11.rz = gbox1.rz * 0.5;
  auto res11 = EvaluateBoxCPU(gbox11, tpool->contacts, tpool->gpu_triples);

  Print("Child 1.0 (box_depth 74): certified={}, winning_triple={}, margin={:.17g}\n",
        res10.certified, res10.winning_triple, res10.margin);
  Print("Child 1.1 (box_depth 74): certified={}, winning_triple={}, margin={:.17g}\n",
        res11.certified, res11.winning_triple, res11.margin);

  Print(AYELLOW("\n--- Testing shelving difficult leaf to chart0.difficult ---\n"));
  SearchManager mgr;
  SearchNode diff_node = node;
  diff_node.id = mgr.next_node_id++;
  diff_node.depth = 96;
  diff_node.box_depth = 72;
  diff_node.view_depth = 24;
  mgr.stack.clear();
  mgr.stack.push_back(diff_node);
  mgr.max_depth = 96;
  mgr.max_box_depth = 72;
  mgr.max_view_depth = 24;
  mgr.batch_size = 64;
  mgr.resume = false;
  mgr.output_dir = ".artifacts/test_difficult";
  mgr.Run();
}

int main(int argc, char **argv) {
  ANSI::Init();
  InstallSignalHandlers();

  bool run_all = false;
  bool run_solution = false;
  bool run_valley = false;
  bool run_depth_out = false;

  for (int i = 1; i < argc; i++) {
    std::string_view arg = argv[i];
    if (arg == "--test_solution" || arg == "--solution") {
      run_solution = true;
    } else if (arg == "--test_valley" || arg == "--valley") {
      run_valley = true;
    } else if (arg == "--test_depth_out" || arg == "--depth_out") {
      run_depth_out = true;
    } else if (arg == "--all" || arg == "-a") {
      run_all = true;
    } else if (arg == "--help" || arg == "-h") {
      Print("Usage: ./test229.exe [test-flags]\n"
            "  --solution, --test_solution   Verify detection on known Rupert solution 1662\n"
            "  --valley, --test_valley       Test valley point LP evaluation and subdivision\n"
            "  --depth_out, --test_depth_out Test depth-out certification on difficult cell\n"
            "  --all, -a                     Run all tests (default if no flags)\n");
      return 0;
    } else {
      Print("Unknown test arg: %s\nTry ./test229.exe --help\n", argv[i]);
      return -1;
    }
  }

  if (!run_solution && !run_valley && !run_depth_out && !run_all) {
    run_all = true;
  }

  if (run_solution || run_all) {
    Print(ACYAN("=== Running TestKnownSolution ===\n"));
    TestKnownSolution();
  }
  if (run_valley || run_all) {
    Print(ACYAN("=== Running TestValleyPoint ===\n"));
    TestValleyPoint();
  }
  if (run_depth_out || run_all) {
    Print(ACYAN("=== Running TestDepthOut ===\n"));
    TestDepthOut();
  }

  Print(AGREEN("All tests completed successfully.\n"));
  return 0;
}
