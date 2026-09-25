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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo cont0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo cont1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo cont2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo cont3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  ContactInfo cont_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };

  std::vector<vec3> selected;
  std::vector<ContactInfo[3]> selected_conts;
  std::string err;

  // Add u1, u2, u3, u_core
  ContactInfo base[4][3] = {
    {cont1[0], cont1[1], cont1[2]},
    {cont2[0], cont2[1], cont2[2]},
    {cont3[0], cont3[1], cont3[2]},
    {cont_core[0], cont_core[1], cont_core[2]}
  };
  for (int b = 0; b < 4; b++) {
    AxisCertificate ax;
    BigVecQ3 c;
    BigRat d;
    Tube229::AuditAxis(tri, base[b], &ax, &c, &d, &err, BigRat(0));
    selected.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
  }

  // Pre-audit all zero-defect candidate axes
  AxisCertificate ax0;
  BigVecQ3 c0;
  BigRat d0;
  Tube229::AuditAxis(tri, cont0, &ax0, &c0, &d0, &err, BigRat(5, 1000));
  vec3 u0 = {c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};
  vec3 view = {tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()};
  auto cands = Tube229::GenerateCandidatesForView(view, tri, false, 5, false);
  std::vector<vec3> cand_axes;
  std::vector<size_t> cand_indices;
  for (size_t i = 0; i < cands.size(); i++) {
    ContactInfo cont[3] = {cands[i].contacts[0], cands[i].contacts[1], cands[i].contacts[2]};
    AxisCertificate ax;
    BigVecQ3 c;
    BigRat d;
    if (Tube229::AuditAxis(tri, cont, &ax, &c, &d, &err, BigRat(0))) {
      cand_axes.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
      cand_indices.push_back(i);
    }
  }
  std::cout << "Audited " << cand_axes.size() << " valid zero-defect candidate axes\n";

  // Fibonacci sphere test points
  int N = 100000;
  std::vector<vec3> sphere(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    sphere[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  std::vector<double> current_cover(N);
  for (int i = 0; i < N; i++) {
    double m = -999.0;
    for (const auto &u : selected) {
      double d = yocto::dot(sphere[i], u);
      if (d > m) m = d;
    }
    current_cover[i] = m;
  }

  while (true) {
    double min_cov = 999.0;
    int worst_i = -1;
    for (int i = 0; i < N; i++) {
      if (current_cover[i] < min_cov) {
        min_cov = current_cover[i];
        worst_i = i;
      }
    }
    std::cout << "Current min coverage with " << selected.size() << " axes: " << min_cov << "\n";
    if (min_cov > 0.002) break;

    // Find axis that maximizes coverage at worst_i
    int best_c = -1;
    double best_val = -999.0;
    for (size_t c = 0; c < cand_axes.size(); c++) {
      double d = yocto::dot(sphere[worst_i], cand_axes[c]);
      if (d > best_val) {
        best_val = d;
        best_c = c;
      }
    }
    std::cout << "Worst point: (" << sphere[worst_i].x << ", " << sphere[worst_i].y << ", " << sphere[worst_i].z << ")\n";
    std::cout << "dot with u0 = " << yocto::dot(sphere[worst_i], u0) << "\n";
    std::cout << "Adding candidate " << cand_indices[best_c] << " with worst-point dot = " << best_val << "\n";
    if (best_val <= 0) {
      std::cout << "No zero-defect candidate has positive dot product at this point!\n";
      break;
    }
    // update current_cover
    for (int i = 0; i < N; i++) {
      double d = yocto::dot(sphere[i], cand_axes[best_c]);
      if (d > current_cover[i]) current_cover[i] = d;
    }
  }

  std::cout << "SUCCESS! Found set of " << selected.size() << " zero-defect axes with min coverage > 0.002!\n";
  return 0;
}
