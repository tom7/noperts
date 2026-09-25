#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <thread>
#include <atomic>
#include <chrono>
#include <memory>
#include <filesystem>
#include <shared_mutex>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"

using namespace tubetree229;

struct WorkerStats {
  uint64_t leaves_certified = 0;
  uint64_t instant_hits = 0;
  uint64_t full_synths = 0;
  uint64_t splits = 0;
  uint64_t failed = 0;
};

// Depth-first certificate search with rollback on failure
bool DfsCertify(TreeNode *node, int max_depth,
                std::vector<Tube229::CandidateTriple> &local_axes,
                std::optional<TubeCertificate> &local_cert,
                WorkerStats &stats) {
  TriangleQ tri = node->GetTriangle();
  int depth = node->path.length();

  // 1. Fast audit using parent/sibling winning certificate
  if (local_cert.has_value()) {
    TubeCertificate cert;
    if (Tube229::AuditCertificateAdaptive(tri, *local_cert, &cert)) {
      node->direct_cert = cert;
      node->direct_bounds.direct_r_lower = cert.r;
      node->direct_bounds.direct_c_lower = cert.c;
      stats.leaves_certified++;
      stats.instant_hits++;
      return true;
    }
  }

  // 2. Full iterative synthesis warm-started with winning axes
  TubeCertificate cert;
  bool ok = Tube229::SynthesizeCertificateIterative(
      tri, depth, &cert, /*extra_contacts=*/{}, /*extra_axes=*/local_axes);

  if (ok) {
    node->direct_cert = cert;
    node->direct_bounds.direct_r_lower = cert.r;
    node->direct_bounds.direct_c_lower = cert.c;
    stats.leaves_certified++;
    stats.full_synths++;

    // Update warm-start cache with axes and cert from this winning result
    local_cert = cert;
    local_axes.clear();
    for (int a = 0; a < 4; a++) {
      Tube229::CandidateTriple ct;
      ct.contacts[0] = cert.axes[a].contacts[0];
      ct.contacts[1] = cert.axes[a].contacts[1];
      ct.contacts[2] = cert.axes[a].contacts[2];
      local_axes.push_back(ct);
    }
    return true;
  }

  if (depth >= max_depth) {
    stats.failed++;
    return false;
  }

  // 3. Subdivide into 4 children and recurse depth-first
  stats.splits++;
  node->children.resize(4);
  for (int c = 0; c < 4; c++) {
    node->children[c] = std::make_unique<TreeNode>();
    node->children[c]->path = node->path + std::to_string(c);
  }

  bool all_children_ok = true;
  for (size_t c = 0; c < node->children.size(); c++) {
    if (!DfsCertify(node->children[c].get(), max_depth, local_axes, local_cert, stats)) {
      all_children_ok = false;
      break;
    }
  }

  if (!all_children_ok) {
    // Clean rollback: revert this branch so no dangling partial trees remain
    node->children.clear();
    return false;
  }

  return true;
}

int main(int argc, char **argv) {
  std::string tree_file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::string prefix_filter = "0312130021121220";
  int num_threads = 16;
  int max_leaves = 0; // 0 = all matching
  int max_dfs_depth = 28;
  int save_interval_sec = 900; // 15 minutes
  bool dry_run = false;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--threads" && i + 1 < argc) num_threads = std::stoi(argv[++i]);
    else if (arg == "--max_leaves" && i + 1 < argc) max_leaves = std::stoi(argv[++i]);
    else if (arg == "--max_dfs_depth" && i + 1 < argc) max_dfs_depth = std::stoi(argv[++i]);
    else if (arg == "--save_interval" && i + 1 < argc) save_interval_sec = std::stoi(argv[++i]);
    else if (arg == "--prefix" && i + 1 < argc) prefix_filter = argv[++i];
    else if (arg == "--tree_file" && i + 1 < argc) tree_file = argv[++i];
    else if (arg == "--dry_run") dry_run = true;
  }

  std::cout << "=========================================================\n";
  std::cout << "Targeted Multi-Threaded DFS Seam Sweeper (16 Threads, Safe Rollback)\n";
  std::cout << "  Tree File:      " << tree_file << "\n";
  std::cout << "  Prefix Filter:  " << (prefix_filter.empty() ? "(none)" : prefix_filter) << "\n";
  std::cout << "  Worker Threads: " << num_threads << "\n";
  std::cout << "  Max Leaves:     " << (max_leaves == 0 ? "ALL" : std::to_string(max_leaves)) << "\n";
  std::cout << "  Max DFS Depth:  " << max_dfs_depth << "\n";
  std::cout << "  Save Interval:  " << save_interval_sec << " s (15 min)\n";
  std::cout << "  Dry Run:        " << (dry_run ? "YES" : "NO") << "\n";
  std::cout << "=========================================================\n" << std::flush;

  auto t_load0 = std::chrono::steady_clock::now();
  std::cout << "Loading tree...\n" << std::flush;
  auto root = LoadTreeJson(tree_file, false, "ruperts/.artifacts/nopert229");
  if (!root) {
    std::cerr << "Failed to load " << tree_file << "\n";
    return 1;
  }
  auto t_load1 = std::chrono::steady_clock::now();
  std::cout << "Tree loaded in "
            << std::chrono::duration<double>(t_load1 - t_load0).count() << " s\n" << std::flush;

  // Find a good seed certificate from an existing certified node
  std::optional<TubeCertificate> seed_cert;
  auto find_seed = [&](auto &self, TreeNode *node) -> void {
    if (!node || seed_cert.has_value()) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) {
      seed_cert = *node->direct_cert;
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  find_seed(find_seed, root.get());
  if (seed_cert) {
    std::cout << "Found seed certificate in tree: r=" << seed_cert->r.ToString() << "\n" << std::flush;
  }

  // Collect uncertified leaves matching prefix
  std::vector<TreeNode*> uncert_leaves;
  auto collect = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->children.empty()) {
      if (!node->direct_cert.has_value()) {
        if (prefix_filter.empty() || node->path.starts_with(prefix_filter)) {
          uncert_leaves.push_back(node);
        }
      }
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  std::cout << "Matching uncertified leaves in tree: " << uncert_leaves.size() << "\n" << std::flush;
  if (uncert_leaves.empty()) {
    std::cout << "Nothing to do! All matching leaves are certified.\n";
    return 0;
  }

  size_t target_count = uncert_leaves.size();
  if (max_leaves > 0 && max_leaves < (int)target_count) {
    target_count = max_leaves;
  }

  std::cout << "Processing " << target_count << " leaves with " << num_threads << " threads...\n\n" << std::flush;

  std::atomic<size_t> next_idx{0};
  std::atomic<size_t> completed_count{0};
  std::vector<WorkerStats> worker_stats(num_threads);
  std::vector<std::thread> workers;
  std::shared_mutex tree_mutex;
  std::atomic<bool> done{false};

  auto t_start = std::chrono::steady_clock::now();

  for (int t = 0; t < num_threads; t++) {
    workers.emplace_back([&, t]() {
      std::vector<Tube229::CandidateTriple> local_axes;
      std::optional<TubeCertificate> local_cert = seed_cert;

      if (local_cert.has_value()) {
        for (int a = 0; a < 4; a++) {
          Tube229::CandidateTriple ct;
          ct.contacts[0] = local_cert->axes[a].contacts[0];
          ct.contacts[1] = local_cert->axes[a].contacts[1];
          ct.contacts[2] = local_cert->axes[a].contacts[2];
          local_axes.push_back(ct);
        }
      }

      while (true) {
        size_t idx = next_idx.fetch_add(1);
        if (idx >= target_count) break;
        TreeNode *leaf = uncert_leaves[idx];

        std::shared_lock<std::shared_mutex> lock(tree_mutex);
        DfsCertify(leaf, max_dfs_depth, local_axes, local_cert, worker_stats[t]);
        completed_count.fetch_add(1);
      }
    });
  }

  // Monitor thread for live visible progress and 15-minute periodic checkpoints
  std::thread monitor([&]() {
    auto last_save = std::chrono::steady_clock::now();

    while (!done) {
      std::this_thread::sleep_for(std::chrono::seconds(2));
      size_t cur = completed_count.load();
      if (cur > target_count) cur = target_count;

      uint64_t total_leaves = 0, total_splits = 0, total_fails = 0, total_hits = 0, total_synths = 0;
      for (int t = 0; t < num_threads; t++) {
        total_leaves += worker_stats[t].leaves_certified;
        total_splits += worker_stats[t].splits;
        total_fails += worker_stats[t].failed;
        total_hits += worker_stats[t].instant_hits;
        total_synths += worker_stats[t].full_synths;
      }

      auto now = std::chrono::steady_clock::now();
      double elapsed = std::chrono::duration<double>(now - t_start).count();
      double rate = elapsed > 0 ? (cur / elapsed) : 0;
      double remaining = (rate > 0 && cur < target_count) ? ((target_count - cur) / rate) : 0;

      double pct = target_count > 0 ? (100.0 * cur / target_count) : 100.0;
      std::cout << std::fixed << std::setprecision(1);
      std::cout << "[PROGRESS] " << cur << " / " << target_count << " (" << pct << "%)"
                << " | Rate: " << rate << " leaves/s"
                << " | Cert Leaves: " << total_leaves << " (hits: " << total_hits << ", synths: " << total_synths << ")"
                << " | Splits: " << total_splits
                << " | Fails: " << total_fails
                << " | Remaining: " << (int)remaining << "s\n" << std::flush;

      // Check if 15 minutes have elapsed since last save
      double elapsed_since_save = std::chrono::duration<double>(now - last_save).count();
      if (!dry_run && elapsed_since_save >= save_interval_sec && total_leaves > 0) {
        last_save = now;
        std::cout << "\n[CHECKPOINT] 15-minute checkpoint triggered. Saving tree to disk...\n" << std::flush;
        std::unique_lock<std::shared_mutex> lock(tree_mutex);
        std::string tmp_file = tree_file + ".checkpoint.tmp";
        if (SaveTreeJson(*root, tmp_file, /*shallow=*/false)) {
          std::filesystem::rename(tmp_file, tree_file);
          std::cout << "[CHECKPOINT] SUCCESS: Checkpoint tree saved to " << tree_file << "\n\n" << std::flush;
        } else {
          std::cerr << "[CHECKPOINT] ERROR: Failed to save checkpoint to " << tmp_file << "\n\n" << std::flush;
        }
      }
    }
  });

  for (auto &w : workers) {
    w.join();
  }
  done = true;
  monitor.join();

  auto t_end = std::chrono::steady_clock::now();
  double total_time = std::chrono::duration<double>(t_end - t_start).count();

  uint64_t total_leaves = 0, total_splits = 0, total_fails = 0, total_hits = 0, total_synths = 0;
  for (int t = 0; t < num_threads; t++) {
    total_leaves += worker_stats[t].leaves_certified;
    total_splits += worker_stats[t].splits;
    total_fails += worker_stats[t].failed;
    total_hits += worker_stats[t].instant_hits;
    total_synths += worker_stats[t].full_synths;
  }

  std::cout << "\n=========================================================\n";
  std::cout << "Targeted DFS Run Completed\n";
  std::cout << "  Target Leaves Processed: " << target_count << "\n";
  std::cout << "  Total Elapsed Time:      " << total_time << " s\n";
  std::cout << "  Newly Certified Leaves:  " << total_leaves << "\n";
  std::cout << "    - Instant Fast Audits: " << total_hits << "\n";
  std::cout << "    - Full Iterative Synths: " << total_synths << "\n";
  std::cout << "  Internal Node Splits:    " << total_splits << "\n";
  std::cout << "  Failed Subtrees:         " << total_fails << " (cleanly rolled back)\n";
  std::cout << "=========================================================\n" << std::flush;

  if (!dry_run && total_leaves > 0) {
    std::unique_lock<std::shared_mutex> lock(tree_mutex);
    std::string bak_file = tree_file + ".bak_dfs";
    std::cout << "Creating backup: " << bak_file << "...\n" << std::flush;
    std::filesystem::copy_file(tree_file, bak_file, std::filesystem::copy_options::overwrite_existing);

    std::string tmp_file = tree_file + ".tmp";
    std::cout << "Saving updated tree to: " << tmp_file << "...\n" << std::flush;
    if (SaveTreeJson(*root, tmp_file, /*shallow=*/false)) {
      std::filesystem::rename(tmp_file, tree_file);
      std::cout << "SUCCESS: Updated tree written to " << tree_file << "\n";
    } else {
      std::cerr << "ERROR: Failed to save " << tmp_file << "\n";
    }
  }

  return 0;
}
