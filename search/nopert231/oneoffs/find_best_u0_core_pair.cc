#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> std_mixes = {0, 200, 333, 400, 500, 600, 666, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  std::cout << "Silhouette contacts: " << contacts.size() << "\n";

  // Generate candidate triples
  auto candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);
  std::cout << "Candidate triples: " << candidates.size() << "\n";

  struct AxisInfo {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    vec3 u;
    vec3 dir;
    double len;
    double defect;
  };

  std::vector<AxisInfo> zero_defect_axes;
  std::vector<AxisInfo> annular_axes;

  std::string err;
  for (size_t i = 0; i < candidates.size(); i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    // Check if zero-defect axis:
    if (Tube229::AuditAxis(tri, candidates[i].contacts, &ax, &ctr, &del, &err, BigRat(0))) {
      AxisInfo ai;
      for (int k = 0; k < 3; k++) ai.contacts[k] = candidates[i].contacts[k];
      ai.cert = ax; ai.center = ctr; ai.delta = del;
      ai.u = {ctr.x.ToDouble() / ax.B.ToDouble(),
              ctr.y.ToDouble() / ax.B.ToDouble(),
              ctr.z.ToDouble() / ax.B.ToDouble()};
      ai.len = yocto::length(ai.u);
      ai.dir = ai.u / ai.len;
      ai.defect = 0;
      zero_defect_axes.push_back(ai);
    }
  }
  std::cout << "Found " << zero_defect_axes.size() << " zero-defect axes.\n";

  // Now find pairs (i, j) among zero_defect_axes:
  // Can an axis i serve as BOTH annular axis and core axis (i.e. i == j)?
  // For i == j: theta = 0, so window is [0, 4/7 ||u||]!
  // The only requirement is that there exist 3 other complement axes that cage i!
  // Let us sort zero_defect_axes by ||u|| descending:
  std::sort(zero_defect_axes.begin(), zero_defect_axes.end(),
            [](const AxisInfo &a, const AxisInfo &b) { return a.len > b.len; });

  std::cout << "Top 10 zero-defect axes by ||u||:\n";
  for (int k = 0; k < std::min(10, (int)zero_defect_axes.size()); k++) {
    std::cout << "  [" << k << "]: ||u|| = " << zero_defect_axes[k].len
              << ", 4/7||u|| = " << (4.0 / 7.0 * zero_defect_axes[k].len)
              << ", delta = " << zero_defect_axes[k].delta.ToDouble() << "\n";
  }

  return 0;
}
