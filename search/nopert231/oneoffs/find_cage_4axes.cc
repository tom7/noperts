#include <iostream>
#include <vector>
#include <cmath>
#include <random>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

struct AxisInfo {
  ContactInfo triple[3];
  AxisCertificate cert;
  BigVecQ3 center;
  vec3 c_f;
};

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 200, 400, 500, 600, 800, 1000}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    cand_contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  int C = cand_contacts.size();
  std::vector<AxisInfo> axes;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          BigVecQ3 norm_c = center / ax.B;
          axes.push_back({
            {triple[0], triple[1], triple[2]},
            ax, center,
            {norm_c.x.ToDouble(), norm_c.y.ToDouble(), norm_c.z.ToDouble()}
          });
        }
      }
    }
  }

  std::cout << "Audited " << axes.size() << " zero-defect axes.\n";

  vec3 mean_c = {0, 0, 0};
  vec3 min_c = {1e9, 1e9, 1e9};
  vec3 max_c = {-1e9, -1e9, -1e9};
  for (const auto &a : axes) {
    mean_c = mean_c + a.c_f;
    min_c.x = std::min(min_c.x, a.c_f.x);
    min_c.y = std::min(min_c.y, a.c_f.y);
    min_c.z = std::min(min_c.z, a.c_f.z);
    max_c.x = std::max(max_c.x, a.c_f.x);
    max_c.y = std::max(max_c.y, a.c_f.y);
    max_c.z = std::max(max_c.z, a.c_f.z);
  }
  mean_c = mean_c * (1.0 / axes.size());
  std::cout << "Centroid of zero-defect axes: (" << mean_c.x << ", " << mean_c.y << ", " << mean_c.z << ")\n";
  std::cout << "Bounding box: X in [" << min_c.x << ", " << max_c.x << "], Y in ["
            << min_c.y << ", " << max_c.y << "], Z in [" << min_c.z << ", " << max_c.z << "]\n";

  // Partition axes into 8 octants:
  std::vector<int> octants[8];
  for (size_t i = 0; i < axes.size(); i++) {
    int oct = (axes[i].c_f.x >= 0 ? 1 : 0) |
              (axes[i].c_f.y >= 0 ? 2 : 0) |
              (axes[i].c_f.z >= 0 ? 4 : 0);
    octants[oct].push_back(i);
  }

  std::cout << "Octant sizes:\n";
  for (int o = 0; o < 8; o++) {
    std::cout << "  octant " << o << ": " << octants[o].size() << " axes\n";
  }

  // Pick one from octant 7 (+,+,+), one from octant 0 (-,-,-),
  // and complementary pairs from (-,+,+) and (+,-,-):
  int successes = 0;
  int enclosing_count = 0;
  std::mt19937 rng(42);

  // Loop over all combinations of 4 non-empty octants:
  std::vector<std::array<int, 4>> tetra_octs;
  for (int o0 = 0; o0 < 8; o0++) {
    if (octants[o0].empty()) continue;
    for (int o1 = o0 + 1; o1 < 8; o1++) {
      if (octants[o1].empty()) continue;
      for (int o2 = o1 + 1; o2 < 8; o2++) {
        if (octants[o2].empty()) continue;
        for (int o3 = o2 + 1; o3 < 8; o3++) {
          if (octants[o3].empty()) continue;
          tetra_octs.push_back({o0, o1, o2, o3});
        }
      }
    }
  }
  std::cout << "Testing " << tetra_octs.size() << " octant combinations...\n";

  for (const auto &to : tetra_octs) {
    for (int trial = 0; trial < 2000; trial++) {
      int i0 = octants[to[0]][rng() % octants[to[0]].size()];
      int i1 = octants[to[1]][rng() % octants[to[1]].size()];
      int i2 = octants[to[2]][rng() % octants[to[2]].size()];
      int i3 = octants[to[3]][rng() % octants[to[3]].size()];

      vec3 v0 = axes[i0].c_f;
      vec3 v1 = axes[i1].c_f;
      vec3 v2 = axes[i2].c_f;
      vec3 v3 = axes[i3].c_f;

      double V0 = yocto::dot(v1, yocto::cross(v2, v3));
      double V1 = -yocto::dot(v0, yocto::cross(v2, v3));
      double V2 = yocto::dot(v0, yocto::cross(v1, v3));
      double V3 = -yocto::dot(v0, yocto::cross(v1, v2));

      double total = V0 + V1 + V2 + V3;
      if (std::abs(total) < 1e-6) continue;

      if (total < 0) {
        total = -total;
        V0 = -V0;
        V1 = -V1;
        V2 = -V2;
        V3 = -V3;
      }

      double l0 = V0 / total;
      double l1 = V1 / total;
      double l2 = V2 / total;
      double l3 = V3 / total;

      static int samples_seen = 0;
      samples_seen++;
      if (samples_seen <= 5) {
        std::cout << "Sample #" << samples_seen << ": total=" << total
                  << " l = (" << l0 << ", " << l1 << ", " << l2 << ", " << l3 << ")\n";
      }

      if (l0 > 0.01 && l1 > 0.01 && l2 > 0.01 && l3 > 0.01) {
        enclosing_count++;
        TubeCertificate test_cert;
        test_cert.axes[0] = axes[i0].cert;
        test_cert.axes[1] = axes[i1].cert;
        test_cert.axes[2] = axes[i2].cert;
        test_cert.axes[3] = axes[i3].cert;

        TubeCertificate verified_cert;
        std::string fail;
        if (Tube229::AuditCertificateAdaptive(tri, test_cert, &verified_cert, &fail)) {
          std::cout << "SUCCESS! Valid 4-axis cage on trial " << trial << "!\n";
          std::cout << "  c = " << verified_cert.c.ToString() << "\n";
          std::cout << "  r = " << verified_cert.r.ToString() << "\n";
          successes++;
          if (successes >= 3) break;
        } else if (enclosing_count <= 5) {
          std::cout << "Enclosing #" << enclosing_count << " audit fail: " << fail << "\n";
        }
      }
    }
    if (successes >= 3) break;
  }

  std::cout << "Enclosing tetrahedra tested: " << enclosing_count << ", successes: " << successes << "\n";


  std::cout << "Done. Total successes: " << successes << "\n";
  return 0;
}
