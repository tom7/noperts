#include <iostream>
#include <vector>
#include <string>
#include <chrono>

#include "tube229.h"
#include "tubetree229.h"
#include "annular229.h"

using namespace tubetree229;
using namespace annular229;

int main() {
  std::vector<std::string> pending_paths = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332",
  };

  std::cout << "============================================================\n";
  std::cout << "TESTING ANNULAR SYNTHESIS ON ALL 6 PENDING TRIANGLES\n";
  std::cout << "============================================================\n";

  // Common seed complement axes from sibling analysis
  std::vector<AxisCertificate> seed_axes(3);
  seed_axes[0].contacts[0] = {2, 1, 1, 4, 0, 1};
  seed_axes[0].contacts[1] = {10, 15, 15, 19, 500, 15};
  seed_axes[0].contacts[2] = {3, 2, 2, 1, 0, 2};
  seed_axes[0].nonzero_witness[0] = 15; seed_axes[0].nonzero_witness[1] = 1; seed_axes[0].nonzero_witness[2] = 10;
  seed_axes[0].B = BigRat(128900569, 200000000);

  seed_axes[1].contacts[0] = {2, 1, 1, 4, 0, 1};
  seed_axes[1].contacts[1] = {10, 15, 15, 19, 666, 15};
  seed_axes[1].contacts[2] = {3, 2, 2, 1, 0, 2};
  seed_axes[1].nonzero_witness[0] = 15; seed_axes[1].nonzero_witness[1] = 1; seed_axes[1].nonzero_witness[2] = 10;
  seed_axes[1].B = BigRat(38424249, 50000000);

  seed_axes[2].contacts[0] = {2, 1, 1, 4, 0, 1};
  seed_axes[2].contacts[1] = {1, 4, 4, 8, 333, 4};
  seed_axes[2].contacts[2] = {15, 19, 19, 3, 1000, 19};
  seed_axes[2].nonzero_witness[0] = 15; seed_axes[2].nonzero_witness[1] = 19; seed_axes[2].nonzero_witness[2] = 4;
  seed_axes[2].B = BigRat(245064413, 500000000);

  // The 5 core flock axes verified on 03121303200
  std::vector<AxisCertificate> core_flock(5);
  core_flock[0].contacts[0] = {3, 2, 2, 1, 0, 2};
  core_flock[0].contacts[1] = {1, 4, 4, 8, 800, 4};
  core_flock[0].contacts[2] = {10, 15, 15, 19, 333, 15};
  core_flock[0].nonzero_witness[0] = 10; core_flock[0].nonzero_witness[1] = 15; core_flock[0].nonzero_witness[2] = 1;
  core_flock[0].B = BigRat(578456463, 1000000000);

  core_flock[1].contacts[0] = {2, 1, 1, 4, 0, 1};
  core_flock[1].contacts[1] = {10, 15, 15, 19, 800, 15};
  core_flock[1].contacts[2] = {19, 3, 3, 2, 200, 3};
  core_flock[1].nonzero_witness[0] = 15; core_flock[1].nonzero_witness[1] = 1; core_flock[1].nonzero_witness[2] = 9;
  core_flock[1].B = BigRat(96698479, 50000000);

  core_flock[2].contacts[0] = {3, 2, 2, 1, 0, 2};
  core_flock[2].contacts[1] = {1, 4, 4, 8, 1000, 4};
  core_flock[2].contacts[2] = {10, 15, 15, 19, 333, 15};
  core_flock[2].nonzero_witness[0] = 10; core_flock[2].nonzero_witness[1] = 15; core_flock[2].nonzero_witness[2] = 1;
  core_flock[2].B = BigRat(28646969, 50000000);

  core_flock[3].contacts[0] = {2, 1, 1, 4, 0, 1};
  core_flock[3].contacts[1] = {10, 15, 15, 19, 666, 15};
  core_flock[3].contacts[2] = {19, 3, 3, 2, 0, 3};
  core_flock[3].nonzero_witness[0] = 15; core_flock[3].nonzero_witness[1] = 1; core_flock[3].nonzero_witness[2] = 10;
  core_flock[3].B = BigRat(38424249, 50000000);

  core_flock[4].contacts[0] = {2, 1, 1, 4, 0, 1};
  core_flock[4].contacts[1] = {1, 4, 4, 8, 333, 4};
  core_flock[4].contacts[2] = {15, 19, 19, 3, 1000, 19};
  core_flock[4].nonzero_witness[0] = 15; core_flock[4].nonzero_witness[1] = 19; core_flock[4].nonzero_witness[2] = 4;
  core_flock[4].B = BigRat(245064413, 500000000);

  for (const auto &path : pending_paths) {
    std::cout << "\n------------------------------------------------------------\n";
    std::cout << "Testing Triangle: " << path << " (depth " << path.length() << ")\n";
    std::cout << "------------------------------------------------------------\n";

    auto t0 = std::chrono::steady_clock::now();
    TriangleQ tri = TriangleFromPath(path);

    // 1. Audit annular axis a0 on this triangle
    ContactInfo c0[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, 200, 14}
    };
    AxisCertificate ax0;
    BigVecQ3 ctr0;
    BigRat del0;
    std::string err;
    bool audit_a0 = Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
    std::cout << "  Annular axis a0 audit: " << (audit_a0 ? "OK" : "FAILED (" + err + ")") << "\n";
    if (audit_a0) {
      std::cout << "    del0 = " << del0.ToDouble() << ", B0 = " << ax0.B.ToDouble() << "\n";
    }

    // Audit the 5 core flock axes on this triangle
    int core_ok = 0;
    for (int k = 0; k < 5; k++) {
      AxisCertificate ax_k;
      BigVecQ3 ctr_k;
      BigRat del_k;
      std::string err_k;
      if (Tube229::AuditAxis(tri, core_flock[k].contacts, &ax_k, &ctr_k, &del_k, &err_k, BigRat(26, 100000))) {
        if (del_k.ToDouble() <= 0.00026) {
          core_ok++;
        }
      }
    }
    std::cout << "  Core flock axes audited OK on this triangle: " << core_ok << " / 5\n";

    // 2. Run Annular Synthesis
    AnnularConfig config;
    config.hull_axes_limit = 50000;
    config.cap_sample_count = 2000;
    config.target_delta = BigRat(195, 1000000);
    config.target_r_min = BigRat(19, 10000);
    config.target_c_cone = BigRat(3, 100);
    config.target_c_core = BigRat(12, 10000);

    std::vector<AxisCertificate> all_seeds = seed_axes;
    for (int k = 0; k < 5; k++) {
      all_seeds.push_back(core_flock[k]);
    }

    auto res = SynthesizeAnnularCertificate(tri, all_seeds, config);
    auto t1 = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();

    std::cout << "  Synthesis Result: success = " << (res.success ? "YES" : "NO")
              << " (" << res.explanation << ")\n";
    std::cout << "  Elapsed Time: " << ms << " ms\n";
    if (res.success) {
      std::cout << "  Core flock size: " << res.cert.core_flock_axes.size() << "\n";
      std::cout << "  Complement cage size: " << res.cert.complement_axes.size() << "\n";
    }
  }

  std::cout << "\n============================================================\n";
  std::cout << "ALL PENDING TRIANGLES TEST COMPLETE\n";
  std::cout << "============================================================\n";
  return 0;
}
