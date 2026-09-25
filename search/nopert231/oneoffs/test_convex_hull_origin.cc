#include <iostream>
#include <string>
#include <vector>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

// Linear programming / Farkas test to check if 0 is in the interior of conv(points)
// i.e., conv(points) contains 0 strictly <=> there is NO separating hyperplane:
// there is NO unit normal n such that for all p in points, dot(n, p) <= 0.
// Min-over-sphere of max_i dot(omega, points[i]) > 0.
static bool ContainsOriginStrict(const std::vector<vec3> &pts, double *out_margin) {
  // Test 100,000 points on sphere
  int samples = 100000;
  double golden_ratio = (1.0 + std::sqrt(5.0)) / 2.0;
  double min_max_dot = 1e30;
  vec3 worst_omega = {0, 0, 0};

  for (int i = 0; i < samples; i++) {
    double theta = 2.0 * M_PI * i / golden_ratio;
    double phi = std::acos(1.0 - 2.0 * (i + 0.5) / samples);
    vec3 omega = {std::cos(theta) * std::sin(phi), std::sin(theta) * std::sin(phi), std::cos(phi)};

    double max_d = -1e30;
    for (const auto &p : pts) {
      double d = yocto::dot(omega, yocto::normalize(p));
      if (d > max_d) max_d = d;
    }
    if (max_d < min_max_dot) {
      min_max_dot = max_d;
      worst_omega = omega;
    }
  }

  if (out_margin) *out_margin = min_max_dot;
  std::cout << "    worst omega: (" << worst_omega.x << ", " << worst_omega.y << ", " << worst_omega.z << ")\n";
  return min_max_dot > 0;
}

int main() {
  std::unique_ptr<TreeNode> root = LoadTreeJson(".artifacts/nopert229/tree_0.json", true, ".artifacts/nopert229");
  if (!root) {
    std::cerr << "Failed to load tree_0.json\n";
    return 1;
  }

  std::vector<std::string> paths = {
    "3121300",
    "3121303021",
    "3121303022",
    "3121303023",
    "3121303200",
    "312130332"
  };

  for (const auto &p : paths) {
    const TreeNode *n = root.get();
    for (char ch : p) {
      int idx = ch - '0';
      n = n->children[idx].get();
    }
    std::cout << "\nPath " << p << ":\n";
    if (!n->decomposed_cert.has_value()) {
      std::cout << "  No decomposed cert\n";
      continue;
    }
    const auto &dec = *n->decomposed_cert;
    std::vector<vec3> pts;
    // 1. Inner core axis center
    vec3 c0 = {dec.inner_core_axis.contacts[0].mix / 1000.0, 0, 0}; // just dummy
    // Let's audit actual center:
    TriangleQ tri = n->GetTriangle();
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    std::string fail;
    ContactInfo triple[3] = {dec.inner_core_axis.contacts[0], dec.inner_core_axis.contacts[1], dec.inner_core_axis.contacts[2]};
    if (Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &fail)) {
      pts.push_back({center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
    }

    // 2. Complement axes centers
    for (size_t a = 0; a < dec.complement_axes.size(); a++) {
      ContactInfo ctriple[3] = {dec.complement_axes[a].contacts[0], dec.complement_axes[a].contacts[1], dec.complement_axes[a].contacts[2]};
      if (Tube229::AuditAxis(tri, ctriple, &cert, &center, &delta, &fail)) {
        pts.push_back({center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
      }
    }

    std::cout << "  Audited " << pts.size() << " axes (1 inner + " << (pts.size() - 1) << " complement).\n";
    for (size_t i = 0; i < pts.size(); i++) {
      vec3 u = yocto::normalize(pts[i]);
      std::cout << "    axis " << i << ": (" << u.x << ", " << u.y << ", " << u.z << ")\n";
    }
    double margin = 0;
    bool contains_0 = ContainsOriginStrict(pts, &margin);
    std::cout << "  Convex hull contains origin: " << (contains_0 ? "YES" : "NO")
              << " (min coverage margin over S^2: " << margin << ")\n";
  }
  return 0;
}
