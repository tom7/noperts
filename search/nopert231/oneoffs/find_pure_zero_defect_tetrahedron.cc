#include <iostream>
#include <vector>
#include <cmath>
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

int main() {
  std::vector<std::string> leaves = {
    "03121300",
    "0312130332",
    "03121303200",
    "03121303021",
    "03121303022",
    "03121303023"
  };

  for (const auto &path : leaves) {
    std::cout << "\n========================================\n";
    std::cout << "Searching for pure zero-defect 4-axis cage on " << path << ":\n";
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
    std::vector<Tube229::AuditedAxis> audited;

    for (int i = 0; i < C; i++) {
      for (int j = i + 1; j < C; j++) {
        for (int k = j + 1; k < C; k++) {
          ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
          AxisCertificate ax;
          BigVecQ3 center;
          BigRat delta;
          std::string err;
          if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
            Tube229::AuditedAxis a;
            a.cert = ax;
            a.center = center;
            a.delta = delta;
            audited.push_back(a);
          }
        }
      }
    }

    std::cout << "Audited " << audited.size() << " zero-defect axes.\n";

    // Deduplicate axes that have very close centers:
    std::vector<Tube229::AuditedAxis> dedup;
    std::vector<vec3> dedup_d;
    for (const auto &a : audited) {
      vec3 v = {a.center.x.ToDouble(), a.center.y.ToDouble(), a.center.z.ToDouble()};
      bool close = false;
      for (const auto &other : dedup_d) {
        if (yocto::length(v - other) < 1e-4) {
          close = true;
          break;
        }
      }
      if (!close) {
        dedup.push_back(a);
        dedup_d.push_back(v);
      }
    }
    std::cout << "Deduplicated to " << dedup.size() << " distinct zero-defect axes.\n";

    std::array<int, 4> simplex;
    vec3 sep_norm;
    if (Tube229::FindBalancedTetrahedron(dedup_d, &simplex, &sep_norm)) {
      std::cout << "FOUND PURE ZERO-DEFECT 4-AXIS CAGE! indices: "
                << simplex[0] << ", " << simplex[1] << ", " << simplex[2] << ", " << simplex[3] << "\n";
      BigVecQ3 exact_pts[4] = {dedup[simplex[0]].center, dedup[simplex[1]].center, dedup[simplex[2]].center, dedup[simplex[3]].center};
      BigRat exact_axis_r = Tube229::ExactTetrahedronAxisRadius(exact_pts);
      BigRat exact_cover_r = exact_axis_r * BigRat(19, 20) * BigRat(4, 7);
      BigRat max_del = std::max({dedup[simplex[0]].delta, dedup[simplex[1]].delta, dedup[simplex[2]].delta, dedup[simplex[3]].delta});
      std::cout << "  exact_axis_r = " << exact_axis_r.ToDouble()
                << ", exact_cover_r = " << exact_cover_r.ToDouble()
                << ", max_delta = " << max_del.ToDouble()
                << ", margin = " << (exact_cover_r - max_del).ToDouble() << "\n";
      if (exact_cover_r > max_del) {
        std::cout << "  ===> CAN BE A STANDARD CERTIFICATE! NO DECOMPOSITION NEEDED! <===\n";
      }
    } else {
      std::cout << "Wolfe's algorithm terminated: separating normal = ("
                << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
      double min_dot = 1e9;
      for (const auto &p : dedup_d) {
        double d = yocto::dot(sep_norm, p);
        if (d < min_dot) min_dot = d;
      }
      std::cout << "  min_dot along sep_norm = " << min_dot << "\n";
    }
  }
  return 0;
}
