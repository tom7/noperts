#include <iostream>
#include <iomanip>
#include <vector>
#include <string>
#include <chrono>
#include <thread>
#include <atomic>
#include <shared_mutex>
#include <filesystem>
#include <algorithm>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

struct WorkerStats {
  uint64_t cache_hits = 0;
  uint64_t fast_synths = 0;
  uint64_t skipped_seam = 0;
};

void ProcessLeaf(TreeNode *leaf,
                 std::vector<TubeCertificate> &local_cache,
                 WorkerStats &stats) {
  TriangleQ tri = leaf->GetTriangle();

  // 1. Try local cache of winning certificates (~15 microseconds)
  for (int j = (int)local_cache.size() - 1; j >= 0; j--) {
    TubeCertificate out_cert;
    if (Tube229::AuditCertificateAdaptive(tri, local_cache[j], &out_cert)) {
      leaf->direct_cert = out_cert;
      leaf->direct_bounds.direct_r_lower = out_cert.r;
      leaf->direct_bounds.direct_c_lower = out_cert.c;
      stats.cache_hits++;
      if (j != (int)local_cache.size() - 1) {
        local_cache.push_back(out_cert);
        if (local_cache.size() > 64) local_cache.erase(local_cache.begin());
      }
      return;
    }
  }

  // 2. Cache missed: try single-view fast synthesis (~5 ms)
  // Discovers the winning axes for a new spherical region and populates the cache.
  // If it's a difficult seam leaf, it returns false in ~5 ms without hanging.
  TubeCertificate new_cert;
  if (Tube229::SynthesizeCertificateFast(tri, leaf->depth(), &new_cert)) {
    leaf->direct_cert = new_cert;
    leaf->direct_bounds.direct_r_lower = new_cert.r;
    leaf->direct_bounds.direct_c_lower = new_cert.c;
    local_cache.push_back(new_cert);
    if (local_cache.size() > 64) local_cache.erase(local_cache.begin());
    stats.fast_synths++;
    return;
  }

  stats.skipped_seam++;
}

int main(int argc, char **argv) {
  std::string tree_file = "ruperts/.artifacts/nopert229/tree_0.json";
  std::string prefix_filter = "";
  int num_threads = 16;
  int max_leaves = 0; // 0 = all
  int start_idx = 0;
  int save_interval_sec = 900; // 15 minutes
  bool dry_run = false;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--threads" && i + 1 < argc) num_threads = std::stoi(argv[++i]);
    else if (arg == "--max_leaves" && i + 1 < argc) max_leaves = std::stoi(argv[++i]);
    else if (arg == "--start_idx" && i + 1 < argc) start_idx = std::stoi(argv[++i]);
    else if (arg == "--prefix" && i + 1 < argc) prefix_filter = argv[++i];
    else if (arg == "--save_interval" && i + 1 < argc) save_interval_sec = std::stoi(argv[++i]);
    else if (arg == "--tree_file" && i + 1 < argc) tree_file = argv[++i];
    else if (arg == "--dry_run") dry_run = true;
  }

  std::cout << "=========================================================\n";
  std::cout << "Fast Multi-Threaded Non-Seam Tree 0 Sweeper\n";
  std::cout << "  Tree File:      " << tree_file << "\n";
  std::cout << "  Prefix Filter:  " << (prefix_filter.empty() ? "(ALL)" : prefix_filter) << "\n";
  std::cout << "  Worker Threads: " << num_threads << "\n";
  std::cout << "  Start Index:    " << start_idx << "\n";
  std::cout << "  Max Leaves:     " << (max_leaves == 0 ? "ALL" : std::to_string(max_leaves)) << "\n";
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

  // 1. Collect seed certificates from existing certified nodes in the tree
  std::vector<TubeCertificate> seed_certs;
  auto collect_seeds = [&](auto &self, TreeNode *node) -> void {
    if (!node || seed_certs.size() >= 256) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) {
      seed_certs.push_back(*node->direct_cert);
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect_seeds(collect_seeds, root.get());
  std::cout << "Seeded cache with " << seed_certs.size() << " existing certificates from tree.\n" << std::flush;

  // 2. Collect uncertified leaves matching prefix filter
  std::vector<TreeNode*> uncert_leaves;
  auto collect = [&](auto &self, TreeNode *node) -> void {
    if (!node) return;
    if (node->direct_cert.has_value() && BigRat::Sign(node->direct_cert->r) > 0) return;
    if (node->children.empty()) {
      if (prefix_filter.empty() || node->path.starts_with(prefix_filter)) {
        uncert_leaves.push_back(node);
      }
      return;
    }
    for (auto &c : node->children) self(self, c.get());
  };
  collect(collect, root.get());

  size_t total_uncert = uncert_leaves.size();
  std::cout << "Matching uncertified leaves: " << total_uncert << "\n" << std::flush;
  if (total_uncert == 0) {
    std::cout << "All matching leaves are already certified!\n";
    return 0;
  }

  size_t target_count = total_uncert;
  if (max_leaves > 0 && (size_t)max_leaves < target_count) {
    target_count = (size_t)max_leaves;
  }
  std::cout << "Processing " << target_count << " leaves with " << num_threads << " threads...\n\n" << std::flush;

  std::atomic<size_t> next_idx{(size_t)start_idx};
  std::atomic<size_t> completed_count{(size_t)start_idx};
  std::vector<WorkerStats> worker_stats(num_threads);
  std::atomic<bool> done{false};
  std::shared_mutex tree_mutex;

  auto t_start = std::chrono::steady_clock::now();

  std::vector<std::thread> workers;
  for (int t = 0; t < num_threads; t++) {
    workers.emplace_back([&, t]() {
      std::vector<TubeCertificate> local_cache = seed_certs;
      while (true) {
        size_t idx = next_idx.fetch_add(1);
        if (idx >= target_count) break;
        TreeNode *leaf = uncert_leaves[idx];

        {
          std::shared_lock<std::shared_mutex> lock(tree_mutex);
          ProcessLeaf(leaf, local_cache, worker_stats[t]);
        }
        completed_count.fetch_add(1);
      }
    });
  }

  // Monitor thread for live visible progress and 15-minute periodic checkpoints
  std::thread monitor([&]() {
    auto last_save = std::chrono::steady_clock::now();
    uint64_t last_saved_cert = 0;

    while (!done) {
      std::this_thread::sleep_for(std::chrono::seconds(2));
      size_t cur = completed_count.load();
      if (cur > target_count) cur = target_count;

      uint64_t total_hits = 0, total_synths = 0, total_skipped = 0;
      for (int t = 0; t < num_threads; t++) {
        total_hits += worker_stats[t].cache_hits;
        total_synths += worker_stats[t].fast_synths;
        total_skipped += worker_stats[t].skipped_seam;
      }
      uint64_t total_certified = total_hits + total_synths;

      auto now = std::chrono::steady_clock::now();
      double elapsed = std::chrono::duration<double>(now - t_start).count();
      double processed_this_run = cur > (size_t)start_idx ? (cur - start_idx) : 0;
      double rate = elapsed > 0 ? (processed_this_run / elapsed) : 0;
      double remaining = (rate > 0 && cur < target_count) ? ((target_count - cur) / rate) : 0;

      double pct = target_count > 0 ? (100.0 * cur / target_count) : 100.0;
      std::cout << std::fixed << std::setprecision(1);
      std::cout << "[PROGRESS] " << cur << " / " << target_count << " (" << pct << "%)"
                << " | Rate: " << (int)rate << " leaves/s"
                << " | Certified: " << total_certified
                << " (hits: " << total_hits << ", synths: " << total_synths << ")"
                << " | Seam: " << total_skipped
                << " | Remaining: " << (int)remaining << "s\n" << std::flush;

      // Check if 15 minutes have elapsed since last save
      double elapsed_since_save = std::chrono::duration<double>(now - last_save).count();
      if (!dry_run && elapsed_since_save >= save_interval_sec && total_certified > last_saved_cert) {
        last_save = now;
        last_saved_cert = total_certified;
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

  uint64_t total_hits = 0, total_synths = 0, total_skipped = 0;
  for (int t = 0; t < num_threads; t++) {
    total_hits += worker_stats[t].cache_hits;
    total_synths += worker_stats[t].fast_synths;
    total_skipped += worker_stats[t].skipped_seam;
  }
  uint64_t newly_certified = total_hits + total_synths;

  std::cout << "\n=========================================================\n";
  std::cout << "Sweep Run Completed\n";
  std::cout << "  Leaves Processed:    " << target_count << "\n";
  std::cout << "  Total Elapsed Time:  " << total_time << " s\n";
  std::cout << "  Effective Rate:      " << (target_count / total_time) << " leaves/s\n";
  std::cout << "  Newly Certified:     " << newly_certified << " (" << (100.0 * newly_certified / target_count) << "%)\n";
  std::cout << "    - Cache Hits:      " << total_hits << "\n";
  std::cout << "    - Fast Synths:     " << total_synths << "\n";
  std::cout << "  Remaining Seam:      " << total_skipped << "\n";
  std::cout << "=========================================================\n" << std::flush;

  if (!dry_run && newly_certified > 0) {
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
