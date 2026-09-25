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

  AxisCertificate ax[4], ax_core;
  BigVecQ3 centers[4], c_core;
  BigRat deltas[4], d_core;
  std::string err;

  Tube229::AuditAxis(tri, cont0, &ax[0], &centers[0], &deltas[0], &err, BigRat(5, 1000));
  for (int a = 1; a < 4; a++) {
    ContactInfo *c = (a == 1) ? cont1 : (a == 2 ? cont2 : cont3);
    Tube229::AuditAxis(tri, c, &ax[a], &centers[a], &deltas[a], &err, BigRat(0));
  }
  Tube229::AuditAxis(tri, cont_core, &ax_core, &c_core, &d_core, &err, BigRat(0));

  vec3 u0 = {centers[0].x.ToDouble(), centers[0].y.ToDouble(), centers[0].z.ToDouble()};
  vec3 u1 = {centers[1].x.ToDouble(), centers[1].y.ToDouble(), centers[1].z.ToDouble()};
  vec3 u2 = {centers[2].x.ToDouble(), centers[2].y.ToDouble(), centers[2].z.ToDouble()};
  vec3 u3 = {centers[3].x.ToDouble(), centers[3].y.ToDouble(), centers[3].z.ToDouble()};
  vec3 u_core = {c_core.x.ToDouble(), c_core.y.ToDouble(), c_core.z.ToDouble()};

  double u0_len = yocto::length(u0);

  std::cout << "Axes loaded successfully!\n";
  std::cout << "u0: len = " << u0_len << " delta = " << deltas[0].ToDouble() << "\n";
  std::cout << "u1: len = " << yocto::length(u1) << " delta = " << deltas[1].ToDouble() << "\n";
  std::cout << "u2: len = " << yocto::length(u2) << " delta = " << deltas[2].ToDouble() << "\n";
  std::cout << "u3: len = " << yocto::length(u3) << " delta = " << deltas[3].ToDouble() << "\n";
  std::cout << "u_core: (" << u_core.x << ", " << u_core.y << ", " << u_core.z << ") len = " << yocto::length(u_core) << "\n";

  // Test coverage of {u1, u2, u3, u_core} across ENTIRE SPHERE
  double min_cover_all_4 = 999.0;
  int N = 500000;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    double max_d = std::max(yocto::dot(a, u1), std::max(yocto::dot(a, u2), std::max(yocto::dot(a, u3), yocto::dot(a, u_core))));
    if (max_d < min_cover_all_4) min_cover_all_4 = max_d;
  }
  std::cout << "Coverage of {u1, u2, u3, u_core} across ENTIRE SPHERE: " << min_cover_all_4 << "\n";

  // For any point a, check if max(u1, u2, u3) >= 0 OR u_core >= 0
  // Specifically, check min over S^2 of max(a · u1, a · u2, a · u3, a · u_core)
  // We already saw Coverage of {u1, u2, u3, u_core} across ENTIRE SPHERE: -0.00690474!
  // Where did that -0.00690474 occur?
  // Let's find the worst-case point!
  vec3 worst_a = {0, 0, 0};
  double worst_cov = 999.0;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - 2.0 * (i + 0.5) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

    double max_d = std::max(yocto::dot(a, u1), std::max(yocto::dot(a, u2), std::max(yocto::dot(a, u3), yocto::dot(a, u_core))));
    if (max_d < worst_cov) {
      worst_cov = max_d;
      worst_a = a;
    }
  }
  std::cout << "Worst coverage of {u1, u2, u3, u_core}: " << worst_cov << "\n";
  std::cout << "at a = (" << worst_a.x << ", " << worst_a.y << ", " << worst_a.z << ")\n";
  std::cout << "dot(worst_a, u0) = " << yocto::dot(worst_a, u0) << "\n";
  std::cout << "cos(worst_a, u0) = " << yocto::dot(worst_a, u0) / u0_len << " (angle = "
            << std::acos(yocto::dot(worst_a, u0) / u0_len) * 180.0 / M_PI << " deg)\n";

  return 0;
}
