#include "base/print.h"
#include "lib229.h"

#include "ansi.h"
#include <cstdlib>
#include <string_view>

// NOTE: Canonical 27-facet rational vertices (exact quad coplanarity + 2^52 power-of-two
// denominators) are implemented in ruperts/codebdd229.cc and exported at
// vertices229_exact27.h / vertices229_exact27.lean. See noteperts/QUAD_FACES.md.

int main(int argc, char **argv) {
  ANSI::Init();
  InstallSignalHandlers();

  SearchManager mgr;

  for (int i = 1; i < argc; i++) {
    std::string_view arg = argv[i];
    if (arg == "--chart" && i + 1 < argc) {
      mgr.chart = std::atoi(argv[++i]);
    } else if (arg == "--batch_size" && i + 1 < argc) {
      mgr.batch_size = std::atoi(argv[++i]);
    } else if (arg == "--max_depth" && i + 1 < argc) {
      mgr.max_depth = std::atoi(argv[++i]);
    } else if (arg == "--max_box_depth" && i + 1 < argc) {
      mgr.max_box_depth = std::atoi(argv[++i]);
    } else if (arg == "--max_view_depth" && i + 1 < argc) {
      mgr.max_view_depth = std::atoi(argv[++i]);
    } else if (arg == "--suspicious_depth" && i + 1 < argc) {
      mgr.suspicious_depth = std::atoi(argv[++i]);
    } else if (arg == "--candidates" && i + 1 < argc) {
      mgr.num_candidates = std::atoi(argv[++i]);
    } else if (arg == "--cone_samples" && i + 1 < argc) {
      mgr.cone_samples = std::atoi(argv[++i]);
    } else if (arg == "--escalate_depth" && i + 1 < argc) {
      mgr.escalate_depth = std::atoi(argv[++i]);
    } else if (arg == "--escalate_cone_samples" && i + 1 < argc) {
      mgr.escalate_cone_samples = std::atoi(argv[++i]);
    } else if (arg == "--deep_escalate_depth" && i + 1 < argc) {
      mgr.deep_escalate_depth = std::atoi(argv[++i]);
    } else if (arg == "--deep_escalate_cone_samples" && i + 1 < argc) {
      mgr.deep_escalate_cone_samples = std::atoi(argv[++i]);
    } else if (arg == "--lp_escalate_depth" && i + 1 < argc) {
      mgr.lp_escalate_depth = std::atoi(argv[++i]);
    } else if (arg == "--lp_escalate_box_depth" && i + 1 < argc) {
      mgr.lp_escalate_box_depth = std::atoi(argv[++i]);
    } else if (arg == "--threads" && i + 1 < argc) {
      mgr.num_threads = std::atoi(argv[++i]);
    } else if (arg == "--output_dir" && i + 1 < argc) {
      mgr.output_dir = argv[++i];
    } else if (arg == "--tube_radius" && i + 1 < argc) {
      mgr.tube_radius = std::atof(argv[++i]);
    } else if (arg == "--split_kappa" && i + 1 < argc) {
      mgr.split_kappa = std::atof(argv[++i]);
    } else if (arg == "--triangle_cache" && i + 1 < argc) {
      g_max_triangle_cache_size = std::atoll(argv[++i]);
    } else if (arg == "--cpu") {
      mgr.use_gpu = false;
    } else if (arg == "--gpu") {
      mgr.use_gpu = true;
    } else if (arg == "--fresh") {
      mgr.resume = false;
    } else if (arg == "--resume") {
      mgr.resume = true;
    } else if (arg == "--no_resume") {
      mgr.resume = false;
    } else if (arg == "--prioritize_related") {
      mgr.prioritize_related = true;
    } else if (arg == "--no_prioritize_related") {
      mgr.prioritize_related = false;
    } else if (arg == "--related_epsilon" && i + 1 < argc) {
      mgr.related_epsilon = std::atof(argv[++i]);
    } else if (arg == "--test_solution" || arg == "--test_valley" || arg == "--test_depth_out") {
      Print("Tests have been moved to ./test229.exe. Run ./test229.exe --help\n");
      return 0;
    } else if (arg == "--help" || arg == "-h") {
      Print("Usage: ./lean229.exe [options]\n"
            "  --chart <0|1|2>     Cayley chart index (default 0)\n"
            "  --batch_size <N>    Batch size for GPU/evaluator (default 32768)\n"
            "  --max_depth <D>     Maximum branch-and-bound tree depth (default 40)\n"
            "  --max_box_depth <D> Maximum Cayley box subdivision depth (default 32)\n"
            "  --max_view_depth <D> Maximum view triangle subdivision depth (default 10)\n"
            "  --suspicious_depth <D> Threshold to report hard points (default 36)\n"
            "  --candidates <N>    Maximum candidate triples to test per box (default 0 = all)\n"
            "  --cone_samples <N>  Silhouette cone samples per vertex (default 8)\n"
            "  --escalate_depth <D> Tree depth to escalate cone samples (default 32)\n"
            "  --escalate_cone_samples <N> Escalated cone samples (default 12)\n"
            "  --deep_escalate_depth <D> Tree depth for second cone escalation (default 38)\n"
            "  --deep_escalate_cone_samples <N> Second escalated cone samples (default 14)\n"
            "  --lp_escalate_depth <D> Tree depth to trigger LP CPU escalation (default 0 = disabled)\n"
            "  --lp_escalate_box_depth <D> Box depth to trigger LP CPU escalation (default 0 = disabled)\n"
            "  --split_kappa <K>   Box-to-view angular diameter split bias (default 1.0)\n"
            "  --triangle_cache <N> Maximum unique triangle pools to cache in RAM (default 20480)\n"
            "  --tube_radius <R>   Identity symmetry tube radius (default 1e-4)\n"
            "  --threads <T>       CPU fallback worker threads (default 8)\n"
            "  --output_dir <DIR>  Output directory for logs and checkpoints\n"
            "  --cpu               Force multi-threaded CPU execution\n"
            "  --gpu               Use OpenCL acceleration (default)\n"
            "  --resume            Resume from checkpoint if present (default)\n"
            "  --fresh             Ignore any checkpoint and start fresh\n"
            "  --test_solution     Verify detection on known Rupert solution 1662\n");
      return -1;
    } else {
      Print("Unknown arg. Try ./lean229.exe --help\n");
      return -1;
    }
  }

  mgr.InitOpenCL();
  mgr.Run();
  return 0;
}
