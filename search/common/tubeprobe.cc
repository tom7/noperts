// Probes the identity-tube cage synthesis (tubecode) on triangles of
// decreasing size around one view: for each size, the best cage that
// tubecode's two searches (FindBestCageForTriangle, SynthesizeCertificate)
// find, audited exactly (ReauditCertificate: cover radius, variation delta,
// net margin c = cover - delta, tube radius). For finding out why a tube
// tree goes deep somewhere (survey5d --tubes), compared with the first-order
// margin there (nopert229's viewmargin).
//
// Triangles: equilateral, centered at the view, in the projective chart
// sum_c sign(u_c) u_c = 1 (the code triangles' charts), with the given
// angular diameters.
//
// Usage: tubeprobe.exe --view x,y,z [--sizes 1e-2,1e-3,...] [--axis_radius] [--verbose]
// --axis_radius: tubecode's --axis_radius (cage objective: the audited axis
// radius, with the brute-force support-point search always on).

#define TUBECODE_NO_MAIN
#include "tubecode.cc"

namespace {

BigRat ToRat(double x) {
  // x to 2^-50 precision.
  const double s = 1125899906842624.0;
  return BigRat(BigInt((int64_t)std::llround(x * s)), BigInt((int64_t)s));
}

std::vector<double> ParseDoubles(const std::string &s) {
  std::vector<double> r;
  size_t p = 0;
  while (p < s.size()) {
    size_t q = s.find(',', p);
    if (q == std::string::npos) q = s.size();
    r.push_back(std::stod(s.substr(p, q - p)));
    p = q + 1;
  }
  return r;
}

void Report(const char *what, const TriangleQ &tri, const LocalCertificate &cert) {
  LocalCertificate out;
  std::string why;
  BigRat cover(-1), delta(-1);
  const bool ok = ReauditCertificate(tri, cert, BigRat(0), BigRat(0), &out, &why, &cover, &delta);
  if (cover < BigRat(0)) {
    printf("    %-10s audit failed: %s\n", what, why.c_str());
    return;
  }
  printf("    %-10s cover %.3e delta %.3e c %.3e r %.3e%s%s\n", what, cover.ToDouble(), delta.ToDouble(),
         (cover - delta).ToDouble(), ok ? out.r.ToDouble() : 0.0, ok ? "" : "  fails: ", ok ? "" : why.c_str());
}

}  // namespace

int main(int argc, char **argv) {
  std::vector<double> view, sizes = {1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 1e-6};
  bool verbose = false;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a;
      return argv[++i];
    };
    if (a == "--view") view = ParseDoubles(next());
    else if (a == "--sizes") sizes = ParseDoubles(next());
    else if (a == "--verbose") verbose = true;
    else if (a == "--axis_radius") g_axis_radius_objective = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(view.size() == 3) << "--view x,y,z";
  vec3 u = yocto::normalize(vec3{view[0], view[1], view[2]});
  // The chart point and two directions in the chart plane.
  const vec3 sg{u.x >= 0 ? 1.0 : -1.0, u.y >= 0 ? 1.0 : -1.0, u.z >= 0 ? 1.0 : -1.0};
  const vec3 p = u / yocto::dot(sg, u);
  vec3 a = yocto::cross(sg, vec3{0, 0, 1});
  if (yocto::length(a) < 0.1) a = yocto::cross(sg, vec3{1, 0, 0});
  a = yocto::normalize(a);
  const vec3 b = yocto::normalize(yocto::cross(sg, a));
  printf("view (%.6f, %.6f, %.6f), chart point (%.6f, %.6f, %.6f)\n", u.x, u.y, u.z, p.x, p.y, p.z);
  unsigned int seed = 1;
  for (double h : sizes) {
    // Angular diameter h at the view: chart lengths scale by |p|.
    const double s = h * yocto::length(p) / std::sqrt(3.0);
    TriangleQ tri;
    for (int k = 0; k < 3; k++) {
      const double th = 2 * M_PI * k / 3 + 0.1;
      const vec3 c = p + s * (std::cos(th) * a + std::sin(th) * b);
      tri.corners[k] = {ToRat(c.x), ToRat(c.y), ToRat(c.z)};
    }
    printf("  size %.1e:\n", h);
    LocalCertificate cert;
    double margin = 0;
    if (FindBestCageForTriangle(tri, &seed, &cert, &margin)) Report("best-cage", tri, cert);
    else printf("    best-cage  none (margin %.3e)\n", margin);
    LocalCertificate syn;
    if (SynthesizeCertificate(tri, 20, BigRat(0), BigRat(0), &syn, verbose)) Report("synthesize", tri, syn);
    else printf("    synthesize none\n");
  }
  return 0;
}
