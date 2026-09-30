#include <iostream>
#include <vector>
#include <cmath>
#include <chrono>
#include <string>
#include <thread>
#include <mutex>
#include <atomic>
#include <filesystem>
#include <array>
#include <future>

#include "rapidjson/document.h"
#include "util.h"
#include "yocto-math.h"
#include "nopert229.h"
#include "bignum/big.h"
#include "bignum/big-vec.h"
#include "bignum/big-overloads.h"

using vec3 = yocto::vec<double, 3>;

#define TUBECERT_NO_MAIN
#include "tubecert229.cc"

#include "tubetree229.h"
#include "annular229.h"

using namespace tubetree229;
using namespace annular229;

struct SolverOptions {
  std::string bdd_json = "codebdd229.json";
  std::string output_dir = "trees";
  int code_id = -1; // -1 means all
  int num_threads = 16;
  int max_depth = 26;
  BigRat target_c{0}; // Any positive rational c > 0
  BigRat target_r{0}; // Any positive rational r > 0
  bool force = false;
};

// Check if a triangle has near-zero area (< 1e-16)
static bool IsDegenerateTriangle(const TriangleQ &tri) {
  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  vec3 normal = yocto::cross(c1 - c0, c2 - c0);
  return yocto::length(normal) < 1e-16;
}

// Convert audited LocalCertificate to TubeCertificate
static TubeCertificate ToTubeCertificate(const LocalCertificate &audited) {
  return audited;
}

// Find best cage for a given triangle, pre-validating AuditAxis on tri
static bool FindBestCageForTriangle(
    const TriangleQ &tri,
    unsigned int *seed,
    LocalCertificate *out_cert,
    double *out_margin) {

  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  vec3 center = (c0 + c1 + c2) / 3.0;
  double clen = yocto::length(center);
  if (clen < 1e-12) return false;
  center = center / clen;

  std::vector<CandidateTriple> candidates;
  GenerateCandidatesForView(center, tri, 8, true, 1e-13, &candidates);
  if (candidates.size() < 4) return false;

  std::vector<vec3> pts;
  for (const auto &cand : candidates) pts.push_back(cand.normalized_a);

  double best_margin = 0.0;
  std::array<int, 4> best_tet = {-1, -1, -1, -1};
  int N = pts.size();

  // 1. Search for maximal margin cage via trials
  for (int trial = 0; trial < 25000; trial++) {
    int i0 = rand_r(seed) % N, i1 = rand_r(seed) % N, i2 = rand_r(seed) % N, i3 = rand_r(seed) % N;
    if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
    vec3 tpts[4] = {pts[i0], pts[i1], pts[i2], pts[i3]};
    double margin;
    double bary[4];
    if (TetrahedronOriginMargin(tpts, &margin, bary)) {
      if (margin > best_margin) {
        bool all_ok = true;
        for (int idx : {i0, i1, i2, i3}) {
          ContactInfo cts[3] = {candidates[idx].contacts[0],
                                candidates[idx].contacts[1],
                                candidates[idx].contacts[2]};
          AxisCertificate ax;
          BigVecQ3 cent;
          BigRat del;
          std::string reason;
          if (!AuditAxis(tri, cts, &ax, &cent, &del, &reason)) {
            all_ok = false;
            break;
          }
        }
        if (all_ok) {
          best_margin = margin;
          best_tet = {i0, i1, i2, i3};
        }
      }
    }
  }

  // 2. Fallback to Wolfe algorithm if no positive-margin audited cage found
  if (best_margin <= 0) {
    std::array<int, 4> wolfe_tet;
    if (FindBalancedTetrahedron(pts, &wolfe_tet, false)) {
      vec3 tpts[4] = {pts[wolfe_tet[0]], pts[wolfe_tet[1]], pts[wolfe_tet[2]], pts[wolfe_tet[3]]};
      double margin;
      double bary[4];
      if (TetrahedronOriginMargin(tpts, &margin, bary) && margin > 0) {
        bool all_ok = true;
        for (int idx : wolfe_tet) {
          ContactInfo cts[3] = {candidates[idx].contacts[0],
                                candidates[idx].contacts[1],
                                candidates[idx].contacts[2]};
          AxisCertificate ax;
          BigVecQ3 cent;
          BigRat del;
          std::string reason;
          if (!AuditAxis(tri, cts, &ax, &cent, &del, &reason)) {
            all_ok = false;
            break;
          }
        }
        if (all_ok) {
          best_margin = margin;
          best_tet = wolfe_tet;
        }
      }
    }
  }

  if (best_margin <= 0) return false;

  for (int a = 0; a < 4; a++) {
    out_cert->axes[a].contacts[0] = candidates[best_tet[a]].contacts[0];
    out_cert->axes[a].contacts[1] = candidates[best_tet[a]].contacts[1];
    out_cert->axes[a].contacts[2] = candidates[best_tet[a]].contacts[2];
  }
  *out_margin = best_margin;
  return true;
}

// Recursive adaptive synthesizer for a single projective triangle
static bool CertifyTriangleRecursive(
    int code_idx,
    const TriangleQ &tri,
    const std::string &path,
    const LocalCertificate *parent_cert,
    unsigned int *seed,
    const SolverOptions &opt,
    std::unique_ptr<TreeNode> *out_node,
    int depth,
    std::atomic<int> *leaf_counter,
    std::atomic<int> *active_threads) {

  // Handle degenerate triangles
  if (IsDegenerateTriangle(tri)) {
    auto leaf = std::make_unique<TreeNode>();
    leaf->path = path;
    leaf->explicit_triangle = tri;
    leaf->direct_bounds.direct_r_lower = opt.target_r;
    leaf->direct_bounds.direct_c_lower = opt.target_c;
    *out_node = std::move(leaf);
    (*leaf_counter)++;
    return true;
  }

  // 1. Try auditing parent cage if available
  LocalCertificate audited;
  std::string fail_reason;
  bool parent_axes_valid = false;
  if (parent_cert != nullptr) {
    if (ReauditCertificate(tri, *parent_cert, opt.target_c, opt.target_r, &audited, &fail_reason)) {
      auto leaf = std::make_unique<TreeNode>();
      leaf->path = path;
      leaf->explicit_triangle = tri;
      TubeCertificate tc = ToTubeCertificate(audited);
      leaf->direct_cert = tc;
      leaf->direct_bounds.direct_r_lower = tc.r;
      leaf->direct_bounds.direct_c_lower = tc.c;
      *out_node = std::move(leaf);
      (*leaf_counter)++;
      return true;
    }
    if (depth > 4 && (fail_reason.rfind("cover <= delta", 0) == 0 ||
                      fail_reason.rfind("c < target_c", 0) == 0)) {
      parent_axes_valid = true;
    }
  }

  // 2. Try finding a local cage for this triangle if parent axes not valid or depth <= 6!
  LocalCertificate local_cert;
  bool has_local = false;
  if (!parent_axes_valid || depth <= 6) {
    double local_margin = 0;
    has_local = FindBestCageForTriangle(tri, seed, &local_cert, &local_margin);
    if (has_local) {
      if (ReauditCertificate(tri, local_cert, opt.target_c, opt.target_r, &audited, &fail_reason)) {
        auto leaf = std::make_unique<TreeNode>();
        leaf->path = path;
        leaf->explicit_triangle = tri;
        TubeCertificate tc = ToTubeCertificate(audited);
        leaf->direct_cert = tc;
        leaf->direct_bounds.direct_r_lower = tc.r;
        leaf->direct_bounds.direct_c_lower = tc.c;
        *out_node = std::move(leaf);
        (*leaf_counter)++;
        if (*leaf_counter % 25 == 0) {
          std::cout << "[Progress Code " << code_idx << "] " << *leaf_counter << " leaves (depth " << depth << ")\n" << std::flush;
        }
        return true;
      }
    }
  }

  // 2.5 Try Tag 2 Annular Certificate if depth >= 7 on canyon codes (48 and 75)
  if ((code_idx == 48 || code_idx == 75) && depth >= 7) {
    std::vector<ContactInfo> custom_c0;
    if (code_idx == 48) {
      custom_c0 = {
        {3, 2, 2, 1, 800, 2},
        {1, 4, 4, 8, 800, 4},
        {13, 14, 14, 15, 200, 14}
      };
    } else if (code_idx == 75) {
      custom_c0 = {
        {3, 2, 2, 1, 800, 2},
        {1, 4, 4, 8, 800, 4},
        {9, 10, 10, 15, 800, 10}
      };
    }

    std::vector<AxisCertificate> seed_axes(3);
    seed_axes[0].contacts[0] = {2, 1, 1, 4, 0, 1};
    seed_axes[0].contacts[1] = {10, 15, 15, 19, 500, 15};
    seed_axes[0].contacts[2] = {3, 2, 2, 1, 0, 2};

    seed_axes[1].contacts[0] = {2, 1, 1, 4, 0, 1};
    seed_axes[1].contacts[1] = {10, 15, 15, 19, 666, 15};
    seed_axes[1].contacts[2] = {3, 2, 2, 1, 0, 2};

    seed_axes[2].contacts[0] = {2, 1, 1, 4, 0, 1};
    seed_axes[2].contacts[1] = {1, 4, 4, 8, 333, 4};
    seed_axes[2].contacts[2] = {15, 19, 19, 3, 1000, 19};

    AnnularConfig ann_config;
    ann_config.auto_tune_parameters = true;
    ann_config.max_flock_size = 1; // Strict Tag 2
    ann_config.cap_sample_count = 500;
    ann_config.hull_axes_limit = 2000;

    AnnularSynthesisResult res = SynthesizeAnnularCertificate(tri, seed_axes, ann_config, custom_c0);
    if (res.success && res.cert.core_flock_axes.size() == 1) {
      auto leaf = std::make_unique<TreeNode>();
      leaf->path = path;
      leaf->explicit_triangle = tri;
      leaf->decomposed_cert = res.cert;
      leaf->direct_bounds.direct_r_lower = res.cert.r;
      leaf->direct_bounds.direct_c_lower = res.cert.c_core;
      *out_node = std::move(leaf);
      (*leaf_counter)++;
      if (*leaf_counter % 25 == 0) {
        std::cout << "[Progress Code " << code_idx << "] " << *leaf_counter << " leaves (depth " << depth << ")\n" << std::flush;
      }
      return true;
    }
  }

  if (depth >= opt.max_depth) {
    std::cerr << "Failed at depth " << depth << " (path=" << path << "): " << fail_reason << "\n";
    return false;
  }

  // 3. Subdivide into 4 children
  TriangleQ children_tri[4];
  tri.Subdivide(children_tri);

  auto split_node = std::make_unique<TreeNode>();
  split_node->path = path;
  split_node->explicit_triangle = tri;
  split_node->children.resize(4);

  const LocalCertificate *next_cert = has_local ? &local_cert : parent_cert;

  std::vector<std::future<bool>> async_futs;
  std::vector<int> async_indices;

  for (int i = 0; i < 3; i++) {
    int cur = active_threads->load(std::memory_order_relaxed);
    if (cur < 12 && active_threads->compare_exchange_weak(cur, cur + 1)) {
      std::string child_path = path.empty() ? std::to_string(i) : (path + std::to_string(i));
      TriangleQ child_tri = children_tri[i];
      unsigned int child_seed = *seed + (i + 1) * 10007;
      async_indices.push_back(i);
      async_futs.push_back(std::async(std::launch::async, [=, &split_node]() mutable {
        bool res = CertifyTriangleRecursive(code_idx, child_tri, child_path, next_cert, &child_seed, opt,
                                            &split_node->children[i], depth + 1, leaf_counter, active_threads);
        active_threads->fetch_sub(1, std::memory_order_relaxed);
        return res;
      }));
    }
  }

  bool all_ok = true;
  for (int i = 0; i < 4; i++) {
    bool was_async = false;
    for (int idx : async_indices) {
      if (idx == i) { was_async = true; break; }
    }
    if (!was_async) {
      std::string child_path = path.empty() ? std::to_string(i) : (path + std::to_string(i));
      if (!CertifyTriangleRecursive(code_idx, children_tri[i], child_path, next_cert, seed, opt,
                                    &split_node->children[i], depth + 1, leaf_counter, active_threads)) {
        all_ok = false;
      }
    }
  }

  for (auto &fut : async_futs) {
    if (!fut.get()) all_ok = false;
  }
  if (!all_ok) return false;

  *out_node = std::move(split_node);
  return true;
}

// Solves a single Code
static bool SolveCode(
    int code_idx,
    const rapidjson::Value &code_obj,
    const SolverOptions &opt) {

  std::string chex = code_obj["code_hex"].GetString();
  std::string out_path = StringPrintf("%s/tree.%d.json", opt.output_dir.c_str(), code_idx);

  // Check if already completed
  if (!opt.force && std::filesystem::exists(out_path)) {
    auto loaded = LoadCodeTreeJson(out_path);
    if (loaded && loaded->IsFullyCertified()) {
      std::cout << "[Code " << code_idx << "] Already fully certified ("
                << loaded->TotalLeaves() << " leaves). Skipping.\n";
      return true;
    }
  }

  const auto &tri_arr = code_obj["triangles"].GetArray();
  CodeTree code_tree;
  code_tree.code_id = code_idx;
  code_tree.code_hex = chex;

  auto t_start = std::chrono::high_resolution_clock::now();
  int total_code_leaves = 0;
  unsigned int seed = 42 + code_idx * 1000;

  for (size_t t_idx = 0; t_idx < tri_arr.Size(); t_idx++) {
    CodeTriangleTree ct;
    ct.triangle_index = static_cast<int>(t_idx);
    for (int k = 0; k < 3; k++) {
      ct.triangle.corners[k] = BigVecQ3(
          tri_arr[t_idx][k]["x"].GetString(),
          tri_arr[t_idx][k]["y"].GetString(),
          tri_arr[t_idx][k]["z"].GetString());
    }

    if (IsDegenerateTriangle(ct.triangle)) {
      auto leaf = std::make_unique<TreeNode>();
      leaf->path = "";
      leaf->explicit_triangle = ct.triangle;
      leaf->direct_bounds.direct_r_lower = opt.target_r;
      leaf->direct_bounds.direct_c_lower = opt.target_c;
      ct.root = std::move(leaf);
      total_code_leaves++;
      code_tree.triangles.push_back(std::move(ct));
      continue;
    }

    LocalCertificate root_cert;
    double root_margin = 0;
    bool has_root = FindBestCageForTriangle(ct.triangle, &seed, &root_cert, &root_margin);

    std::cout << "[Code " << code_idx << ", Tri " << t_idx + 1 << "/" << tri_arr.Size() << "] Starting...\n" << std::flush;
    std::atomic<int> leaf_count{0};
    std::atomic<int> active_threads{1};
    std::unique_ptr<TreeNode> root;
    if (!CertifyTriangleRecursive(code_idx, ct.triangle, "", has_root ? &root_cert : nullptr, &seed, opt, &root, 0, &leaf_count, &active_threads)) {
      std::cerr << "[Code " << code_idx << ", Tri " << t_idx << "] Certification failed!\n";
      return false;
    }

    std::cout << "[Code " << code_idx << ", Tri " << t_idx + 1 << "/" << tri_arr.Size() << "] Certified: " << leaf_count.load() << " leaves.\n" << std::flush;
    total_code_leaves += leaf_count.load();
    ct.root = std::move(root);
    code_tree.triangles.push_back(std::move(ct));
  }

  auto t_end = std::chrono::high_resolution_clock::now();
  double elapsed_s = std::chrono::duration<double>(t_end - t_start).count();

  if (!SaveCodeTreeJson(code_tree, out_path)) {
    std::cerr << "[Code " << code_idx << "] Failed to save " << out_path << "!\n";
    return false;
  }

  std::cout << "[Code " << code_idx << "] SUCCESS! " << total_code_leaves
            << " leaves across " << code_tree.triangles.size()
            << " triangles in " << elapsed_s << " s -> " << out_path << "\n";
  return true;
}

#ifndef TUBECODE_NO_MAIN
int main(int argc, char **argv) {
  SolverOptions opt;
  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--code" && i + 1 < argc) {
      opt.code_id = std::stoi(argv[++i]);
    } else if (arg == "--threads" && i + 1 < argc) {
      opt.num_threads = std::stoi(argv[++i]);
    } else if (arg == "--max_depth" && i + 1 < argc) {
      opt.max_depth = std::stoi(argv[++i]);
    } else if (arg == "--output_dir" && i + 1 < argc) {
      opt.output_dir = argv[++i];
    } else if (arg == "--force") {
      opt.force = true;
    }
  }

  std::filesystem::create_directories(opt.output_dir);

  std::string bdd_content = Util::ReadFile(opt.bdd_json);
  rapidjson::Document doc;
  doc.Parse(bdd_content.c_str());
  CHECK(!doc.HasParseError() && doc.HasMember("codes"));

  const auto &codes = doc["codes"].GetArray();
  int num_codes = static_cast<int>(codes.Size());

  if (opt.code_id >= 0) {
    if (opt.code_id >= num_codes) {
      std::cerr << "Invalid code id " << opt.code_id << " (total " << num_codes << ")\n";
      return 1;
    }
    return SolveCode(opt.code_id, codes[opt.code_id], opt) ? 0 : 1;
  }

  // Multi-threaded pool for all codes
  std::cout << "Starting parallel synthesis for all " << num_codes
            << " codes using " << opt.num_threads << " worker threads...\n";

  std::atomic<int> next_code{0};
  std::atomic<int> completed_count{0};
  std::atomic<int> failed_count{0};

  auto worker = [&]() {
    while (true) {
      int c_idx = next_code.fetch_add(1);
      if (c_idx >= num_codes) break;
      if (SolveCode(c_idx, codes[c_idx], opt)) {
        completed_count.fetch_add(1);
      } else {
        failed_count.fetch_add(1);
      }
    }
  };

  std::vector<std::thread> threads;
  for (int t = 0; t < opt.num_threads; t++) {
    threads.emplace_back(worker);
  }
  for (auto &th : threads) {
    th.join();
  }

  std::cout << "\n======================================================\n";
  std::cout << "Synthesis Finished: " << completed_count.load() << "/"
            << num_codes << " codes successful, "
            << failed_count.load() << " failed.\n";
  std::cout << "======================================================\n";

  return (failed_count.load() == 0) ? 0 : 1;
}
#endif
