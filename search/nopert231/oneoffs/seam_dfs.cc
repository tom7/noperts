#include <iostream>
#include <iomanip>
#include <vector>
#include <string>
#include <string_view>
#include <chrono>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;
using CandidateTriple = Tube229::CandidateTriple;

struct DfsStats {
  int nodes_visited = 0;
  int certified_leaves = 0;
  int fast_audit_hits = 0;
  int full_synth_hits = 0;
  int splits = 0;
  int max_depth_reached = 0;
};

// Global cache of recent winning axes and certificate for instant warm-start audits
static std::vector<CandidateTriple> g_recent_axes;
static std::optional<TubeCertificate> g_recent_cert;

bool DfsCertify(const std::string &path, int max_depth, DfsStats *stats) {
  stats->nodes_visited++;
  int depth = (int)path.size();
  if (depth > stats->max_depth_reached) {
    stats->max_depth_reached = depth;
  }

  TriangleQ tri = TriangleFromPath(path);

  // 1. Fast warm-start audit using recent winning certificate (~15 microseconds)
  if (g_recent_cert.has_value()) {
    TubeCertificate out_cert;
    if (Tube229::AuditCertificateAdaptive(tri, *g_recent_cert, &out_cert)) {
      stats->certified_leaves++;
      stats->fast_audit_hits++;
      std::cout << "  [FAST AUDIT] Depth " << depth << " (" << path << ")"
                << " r=" << out_cert.r.ToString() << " c=" << out_cert.c.ToString() << "\n" << std::flush;
      g_recent_cert = out_cert;
      return true;
    }
  }

  // 2. Synthesize certificate using iterative multi-view & cutting-plane
  TubeCertificate cert;
  bool ok = Tube229::SynthesizeCertificateIterative(
      tri, depth, &cert, /*extra_contacts=*/{}, /*extra_axes=*/g_recent_axes);

  if (ok) {
    stats->certified_leaves++;
    stats->full_synth_hits++;
    std::cout << "  [CERTIFIED] Depth " << depth << " (" << path << ")"
              << " r=" << cert.r.ToString() << " (" << cert.r.ToDouble() << ")"
              << " c=" << cert.c.ToString() << "\n" << std::flush;

    // Update warm-start cache with axes and certificate from this winning result
    g_recent_cert = cert;
    g_recent_axes.clear();
    for (int a = 0; a < 4; a++) {
      CandidateTriple ct;
      ct.contacts[0] = cert.axes[a].contacts[0];
      ct.contacts[1] = cert.axes[a].contacts[1];
      ct.contacts[2] = cert.axes[a].contacts[2];
      g_recent_axes.push_back(ct);
    }
    return true;
  }

  // If not certified, check depth limit
  if (depth >= max_depth) {
    std::cout << "  [FAILED] Depth limit reached at " << path << " (depth " << depth << ")\n" << std::flush;
    return false;
  }

  // 3. Subdivide into 4 children and recurse depth-first
  stats->splits++;
  std::cout << "[SPLIT] Depth " << depth << " (" << path << ") -> recursing children 0..3\n" << std::flush;

  for (int c = 0; c < 4; c++) {
    std::string child_path = path + std::to_string(c);
    bool child_ok = DfsCertify(child_path, max_depth, stats);
    if (!child_ok) {
      // Child failed to certify within max_depth
      return false;
    }
  }

  std::cout << "[COMPLETE] Node " << path << " fully certified via all 4 children!\n" << std::flush;
  return true;
}

int main(int argc, char **argv) {
  std::string target_path = "031213002112122012121";
  int max_depth = 30;

  if (argc > 1) target_path = argv[1];
  if (argc > 2) max_depth = std::stoi(argv[2]);

  std::cout << "=========================================================\n";
  std::cout << "Starting Targeted DFS Seam Search\n";
  std::cout << "  Target Path: " << target_path << " (depth " << target_path.size() << ")\n";
  std::cout << "  Max Depth:   " << max_depth << "\n";
  std::cout << "=========================================================\n" << std::flush;

  // Pre-seed warm-start cache with sibling '0' if target does not end in '0'
  std::string sibling_path = target_path;
  if (!sibling_path.empty() && sibling_path.back() != '0') {
    sibling_path.back() = '0';
    std::cout << "Attempting to pre-seed cache from sibling " << sibling_path << "...\n" << std::flush;
    TubeCertificate sib_cert;
    if (Tube229::SynthesizeCertificateIterative(TriangleFromPath(sibling_path), (int)sibling_path.size(), &sib_cert)) {
      std::cout << "  -> Sibling certified! Pre-seeded cache.\n" << std::flush;
      g_recent_cert = sib_cert;
      for (int a = 0; a < 4; a++) {
        CandidateTriple ct;
        ct.contacts[0] = sib_cert.axes[a].contacts[0];
        ct.contacts[1] = sib_cert.axes[a].contacts[1];
        ct.contacts[2] = sib_cert.axes[a].contacts[2];
        g_recent_axes.push_back(ct);
      }
    }
  }

  auto t0 = std::chrono::steady_clock::now();
  DfsStats stats;
  bool success = DfsCertify(target_path, max_depth, &stats);
  auto t1 = std::chrono::steady_clock::now();

  double elapsed = std::chrono::duration<double>(t1 - t0).count();

  std::cout << "\n=========================================================\n";
  std::cout << "DFS Search " << (success ? "SUCCESSFULLY COMPLETED" : "FAILED") << "\n";
  std::cout << "  Elapsed Time:       " << elapsed << " s\n";
  std::cout << "  Nodes Visited:      " << stats.nodes_visited << "\n";
  std::cout << "  Certified Leaves:   " << stats.certified_leaves << "\n";
  std::cout << "  Splits:             " << stats.splits << "\n";
  std::cout << "  Max Depth Reached:  " << stats.max_depth_reached << "\n";
  std::cout << "=========================================================\n";

  return success ? 0 : 1;
}
