// codebdd.cc: Computes the non-empty visibility codes and their BDD tree for a model.
// Uses exact rational arithmetic (BigVecQ3 / BigRat) and polygon clipping
// to partition the view domain (the model's view triangle) into cells of invariant
// silhouette topology. Generates Farkas infeasibility witnesses on dead branches
// and outputs the full decision tree in JSON format.

#include <algorithm>
#include <array>
#include <bitset>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <format>
#include <fstream>
#include <iostream>
#include <numbers>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

#include "ansi.h"
#include "threadutil.h"
#include "base/logging.h"
#include "base/print.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "geom/hull-2d.h"
#include "model.h"
#include "timer.h"
#include "util.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

// Structure representing an exact rational plane/normal in Q^3
struct PlaneQ {
  int index = -1;
  BigVecQ3 normal;        // Normalized to coprime integers
  BigInt int_x, int_y, int_z;
  std::vector<int> face_vertices; // Polyhedron vertices lying on this face
  bool crosses_view = false;

  std::string ToString() const {
    return std::format("[{}, {}, {}]", int_x.ToString(), int_y.ToString(), int_z.ToString());
  }
};

// Half-space constraint: s * (normal . u) >= 0, where s in {+1, -1}.
struct HalfSpace {
  int plane_idx = -1;  // -1 for the view triangle's edges W0, W1, W2
  int sign = 1;        // +1 (>= 0) or -1 (<= 0)
  BigVecQ3 normal;
  std::string label;
};

// A convex polygon on a projective root's plane (sum_i s_i u_i = 1; the
// clipping only forms affine combinations, so it stays on the plane, and
// every point is a positive multiple of its view direction).
struct ProjectivePoly {
  std::vector<BigVecQ3> vertices;
  // Halfspaces that form the edges of this polygon
  std::vector<HalfSpace> boundary_planes;

  bool IsEmpty() const {
    return vertices.size() < 3;
  }
};

// Farkas contradiction witness for an infeasible branch:
// sum_{i=1}^m lambda_i * vector_i = 0 with lambda_i > 0
struct FarkasWitness {
  struct Term {
    std::string label;
    int plane_idx = -1;
    int sign = 0;
    BigVecQ3 vector;
    BigRat lambda;
  };
  std::vector<Term> terms;
};

// A code: bit i is the sign of plane i (1: u . n >= 0).
inline constexpr int kMaxPlanes = 256;
using Code = std::bitset<kMaxPlanes>;

static Code WithBit(Code c, size_t i) {
  c.set(i);
  return c;
}

// "0x%08X" for up to 32 planes; otherwise all hex digits.
static std::string CodeHex(const Code &c, size_t num_planes) {
  if (num_planes <= 32) return std::format("0x{:08X}", (uint32_t)c.to_ullong());
  std::string hex = "0x";
  for (int nib = ((int)num_planes + 3) / 4 - 1; nib >= 0; nib--) {
    int v = 0;
    for (int b = 3; b >= 0; b--) v = v * 2 + (4 * nib + b < kMaxPlanes && c[4 * nib + b] ? 1 : 0);
    hex += "0123456789ABCDEF"[v];
  }
  return hex;
}

// A leaf node representing a feasible non-empty code cell
struct FeasibleCode {
  int root = 0;  // the projective root of its view triangle (all corners)
  Code code_val;
  std::string hex_id;
  std::string bit_string;
  ProjectivePoly poly;
  std::vector<std::array<BigVecQ3, 3>> triangles;
  std::vector<int> hull_2d_vertices;
};

// BDD Node
struct BDDNode {
  enum Type { BRANCH, INFEASIBLE, FEASIBLE };
  Type type = BRANCH;
  int plane_idx = -1;
  std::unique_ptr<BDDNode> neg_child; // u . n <= 0 (bit = 0)
  std::unique_ptr<BDDNode> pos_child; // u . n >= 0 (bit = 1)
  std::optional<FarkasWitness> witness;
  Code code_val;
  std::string code_hex;
};

// Format a BigRat as a fraction or integer string
std::string FormatRat(const BigRat &r) {
  auto [num, den] = r.Parts();
  if (den == 1) return num.ToString();
  return std::format("{}/{}", num.ToString(), den.ToString());
}

// Nearest multiple of 2^-bits.
static BigRat RoundDyadic(const BigRat &v, int bits) {
  const BigInt scale = BigInt::Pow(BigInt(2), bits);
  auto [num, den] = (v * BigRat(scale, BigInt(1)) + BigRat(1, 2)).Parts();
  return BigRat(BigInt::DivFloor(num, den), scale);
}

// A model file (e.g. septopert_model.txt): the vertices to high precision in C5
// order (vertex S k + s is seed s rotated by 2 pi k / 5), and the faces that
// are not triangles. Lines: "name N", "seeds S", "vertex i x y z",
// "face i j k ...", and others (ignored).
struct ModelFile {
  std::string name;
  int seeds = 0;
  std::vector<std::array<BigRat, 3>> vertices;
  std::vector<std::vector<int>> faces;
  // If given ("rational_vertex i p/q p/q p/q"), the rational model itself,
  // used as is (no rounding or planarization): for models whose faces share
  // vertices, which the generator makes exactly planar together.
  std::vector<BigVecQ3> rational_vertices;
  // The view domain: one or more rational triangles, each in one projective
  // root (Lean's AtlasProjectiveView.rootSign): every corner c satisfies
  // sum_i s_i c_i = 1 and s_i c_i >= 0 for the root's sign vector s.
  // "view_triangle x0 y0 z0 x1 ... z2", one line per triangle.
  std::vector<std::array<BigVecQ3, 3>> view_triangles;
};

// Lean's rootSign order: root = 4 [s0 < 0] + 2 [s1 < 0] + [s2 < 0].
static int RootSign(int root, int c) { return (root >> (2 - c)) & 1 ? -1 : 1; }

// The first projective root containing every corner of t (SignedTriangleValid),
// or -1.
static int TriangleRoot(const std::array<BigVecQ3, 3> &t) {
  for (int root = 0; root < 8; root++) {
    bool ok = true;
    for (const BigVecQ3 &c : t) {
      const BigRat s0(RootSign(root, 0)), s1(RootSign(root, 1)), s2(RootSign(root, 2));
      ok = ok && s0 * c.x >= BigRat(0) && s1 * c.y >= BigRat(0) && s2 * c.z >= BigRat(0) &&
           s0 * c.x + s1 * c.y + s2 * c.z == BigRat(1);
    }
    if (ok) return root;
  }
  return -1;
}

// A decimal string ("-0.1234") as an exact rational.
static BigRat DecimalRat(std::string_view s) {
  bool neg = false;
  if (!s.empty() && (s[0] == '-' || s[0] == '+')) {
    neg = s[0] == '-';
    s.remove_prefix(1);
  }
  const size_t dot = s.find('.');
  std::string digits(s.substr(0, dot));
  size_t frac = 0;
  if (dot != std::string_view::npos) {
    digits += s.substr(dot + 1);
    frac = s.size() - dot - 1;
  }
  CHECK(!digits.empty() && digits.find_first_not_of("0123456789") == std::string::npos) << s;
  BigInt num(digits);
  if (neg) num = BigInt(0) - num;
  return BigRat(num, BigInt::Pow(BigInt(10), frac));
}

static ModelFile LoadModelFile(const std::string &filename) {
  ModelFile m;
  for (const std::string &line : Util::ReadFileToLines(filename)) {
    std::vector<std::string> tok = Util::Tokens(line, [](char c) { return c == ' '; });
    if (tok.empty()) continue;
    if (tok[0] == "name" && tok.size() == 2) {
      m.name = tok[1];
    } else if (tok[0] == "seeds" && tok.size() == 2) {
      m.seeds = std::stoi(tok[1]);
    } else if (tok[0] == "vertex" && tok.size() == 5) {
      CHECK(std::stoi(tok[1]) == (int)m.vertices.size()) << line;
      m.vertices.push_back({DecimalRat(tok[2]), DecimalRat(tok[3]), DecimalRat(tok[4])});
    } else if (tok[0] == "rational_vertex" && tok.size() == 5) {
      CHECK(std::stoi(tok[1]) == (int)m.rational_vertices.size()) << line;
      m.rational_vertices.push_back(BigVecQ3(BigRat(std::string_view(tok[2])),
                                             BigRat(std::string_view(tok[3])),
                                             BigRat(std::string_view(tok[4]))));
    } else if (tok[0] == "face") {
      // (C5 models list only the non-triangular faces; others may list all.)
      std::vector<int> f;
      for (size_t i = 1; i < tok.size(); i++) f.push_back(std::stoi(tok[i]));
      CHECK(f.size() >= 3) << line;
      m.faces.push_back(std::move(f));
    } else if (tok[0] == "view_triangle" && tok.size() == 10) {
      std::array<BigVecQ3, 3> t;
      for (int c = 0; c < 3; c++) {
        t[c] = BigVecQ3(BigRat(std::string_view(tok[1 + 3 * c])), BigRat(std::string_view(tok[2 + 3 * c])),
                        BigRat(std::string_view(tok[3 + 3 * c])));
      }
      CHECK(TriangleRoot(t) >= 0) << "view_triangle is not in one projective root: " << line;
      m.view_triangles.push_back(t);
    }
  }
  // C5 models (seeds S): vertex S k + s is seed s rotated by 2 pi k / 5.
  // Others (no seeds line) must give their rational vertices.
  CHECK(m.seeds == 0 || (int)m.vertices.size() == 5 * m.seeds)
      << filename << ": expected 5 * seeds vertices, got " << m.vertices.size();
  CHECK(m.seeds > 0 || !m.rational_vertices.empty())
      << filename << ": a model without C5 seeds needs rational_vertex lines";
  for (const auto &f : m.faces) for (int v : f) CHECK(v >= 0 && v < (int)m.vertices.size());
  CHECK(m.rational_vertices.empty() || m.rational_vertices.size() == m.vertices.size())
      << filename << ": rational_vertex count";
  return m;
}

// The rational model of a model file: scale to norm just below
// 1 (attempt shifts the scale, and so the rounding), round every coordinate
// to 2^-52, then make every non-triangular face exactly planar by projecting
// its vertices after the first three onto the plane through those, along
// the plane's normal, in exact arithmetic. A face whose vertices already have equal z (a
// horizontal face of one C5 orbit) is planar as rounded. A vertex may be
// moved at most once, and never after it has defined a plane.
static std::vector<BigVecQ3> ModelRationalVertices(const ModelFile &m, int attempt,
                                                   bool verbose) {
  BigRat max_norm2(0);
  for (const auto &v : m.vertices) max_norm2 = std::max(max_norm2, v[0] * v[0] + v[1] * v[1] + v[2] * v[2]);
  // Unit circumradius in the file (checked below): scale 1 - 1e-9 (1 + attempt).
  // (The file's decimals are rounded, so allow 1e-30.)
  CHECK(max_norm2 <= BigRat(1) + BigRat(BigInt(1), BigInt::Pow(BigInt(10), 30)) &&
        max_norm2 > BigRat(999999, 1000000))
      << "circumradius != 1";
  const BigRat scale(BigInt(1000000000 - (1 + attempt)), BigInt(1000000000));
  std::vector<BigRat> target;  // the scaled exact coordinates
  std::vector<BigVecQ3> verts;
  for (const auto &v : m.vertices) {
    BigVecQ3 q(RoundDyadic(v[0] * scale, 52), RoundDyadic(v[1] * scale, 52),
               RoundDyadic(v[2] * scale, 52));
    verts.push_back(q);
  }
  std::vector<char> moved(verts.size(), 0), defined(verts.size(), 0);
  int projected = 0;
  for (const auto &f : m.faces) {
    bool horizontal = true;
    for (int v : f) horizontal = horizontal && verts[v].z == verts[f[0]].z;
    if (horizontal) continue;
    const BigVecQ3 &p0 = verts[f[0]], &p1 = verts[f[1]], &p2 = verts[f[2]];
    for (int k = 0; k < 3; k++) defined[f[k]] = 1;
    const BigVecQ3 n = BigVecQ3::Cross(p1 - p0, p2 - p0);
    const BigRat d = BigVecQ3::Dot(n, p0);
    const BigRat nn = BigVecQ3::Dot(n, n);
    for (size_t k = 3; k < f.size(); k++) {
      const int v = f[k];
      CHECK(!moved[v] && !defined[v]) << "vertex " << v << " is in two non-triangular faces";
      moved[v] = 1;
      verts[v] = verts[v] - n * ((BigVecQ3::Dot(n, verts[v]) - d) / nn);
      CHECK(BigVecQ3::Dot(n, verts[v]) == d);
      projected++;
    }
  }
  // Distance to the exact (scaled) model, exactly.
  const BigRat budget2 = BigRat(6, 10000000000000000LL) * BigRat(6, 10000000000000000LL);
  BigRat worst2(0);
  for (size_t i = 0; i < verts.size(); i++) {
    const BigRat dx = verts[i].x - m.vertices[i][0] * scale, dy = verts[i].y - m.vertices[i][1] * scale,
                 dz = verts[i].z - m.vertices[i][2] * scale;
    worst2 = std::max(worst2, dx * dx + dy * dy + dz * dz);
    CHECK(BigVecQ3::Dot(verts[i], verts[i]) < BigRat(1)) << "vertex " << i << " has norm >= 1";
  }
  CHECK(worst2 <= budget2) << "rational model is " << std::sqrt(worst2.ToDouble())
                           << " from the exact model (budget 6e-16)";
  if (verbose) {
    Print(AGREEN("Rational model of {}:\n"), m.name);
    Print("  {} vertices ({} seeds), quantized to 2^-52, scale 1 - {}e-9\n", verts.size(), m.seeds,
          1 + attempt);
    Print("  {} non-triangular faces made exactly planar ({} vertices projected)\n", m.faces.size(),
          projected);
    Print("  Max distance from the exact model: {:.3e} (budget 6e-16)\n\n",
          std::sqrt(worst2.ToDouble()));
  }
  return verts;
}

// Lean (TightApproximation.lean, stl_tight_sq_close) requires every
// rational vertex to be within 4e-16 of tightVertex, the seed rotated with
// the rational approximations cos72Q, sin72Q. Returns the max distance
// squared, computed exactly.
static BigRat TightVertexDistanceSq(const std::vector<BigVecQ3> &verts) {
  const BigRat cos72("30901699437494745/100000000000000000");
  const BigRat sin72("9510565162951535/10000000000000000");
  const BigRat cos144 = BigRat(2) * cos72 * cos72 - BigRat(1);
  const BigRat sin144 = BigRat(2) * sin72 * cos72;
  const BigRat tc[5] = {BigRat(1), cos72, cos144, cos144, cos72};
  const BigRat ts[5] = {BigRat(0), sin72, sin144, -sin144, -sin72};
  BigRat worst(0);
  const int n = verts.size(), num_seeds = n / 5;
  CHECK(n == 5 * num_seeds);
  for (int i = 0; i < n; i++) {
    const int k = i / num_seeds, sd = i % num_seeds;
    const BigVecQ3 &v = verts[sd];
    const BigRat tx = tc[k] * v.x - ts[k] * v.y;
    const BigRat ty = ts[k] * v.x + tc[k] * v.y;
    const BigRat dx = verts[i].x - tx, dy = verts[i].y - ty, dz = verts[i].z - v.z;
    const BigRat d2 = dx * dx + dy * dy + dz * dz;
    if (d2 > worst) worst = d2;
  }
  return worst;
}

// Models with a C3v symmetry about (1,1,1) (no C5 seeds; c3v_model.py): the
// rotations are the cyclic coordinate permutations, the mirrors the
// transpositions, so the rational vertex set must be exactly invariant
// under every coordinate permutation. Returns, for each permutation in the
// order (x,y,z) -> (y,z,x), (z,x,y), then the transpositions fixing x, y, z
// (Lean's c3Mat 1, c3Mat 2, mirrorMat 0, 1, 2), the induced vertex
// permutation; empty if the set is not invariant.
static std::vector<std::vector<int>> C3vVertexPermutations(const std::vector<BigVecQ3> &verts) {
  auto apply = [](int g, const BigVecQ3 &v) {
    switch (g) {
    case 0: return BigVecQ3(v.y, v.z, v.x);  // c3Mat 1 v
    case 1: return BigVecQ3(v.z, v.x, v.y);  // c3Mat 2 v
    case 2: return BigVecQ3(v.x, v.z, v.y);  // mirrorMat 0 v
    case 3: return BigVecQ3(v.z, v.y, v.x);  // mirrorMat 1 v
    default: return BigVecQ3(v.y, v.x, v.z); // mirrorMat 2 v
    }
  };
  std::vector<std::vector<int>> perms;
  for (int g = 0; g < 5; g++) {
    std::vector<int> p;
    for (const BigVecQ3 &v : verts) {
      const BigVecQ3 w = apply(g, v);
      int hit = -1;
      for (size_t j = 0; j < verts.size(); j++)
        if (verts[j].x == w.x && verts[j].y == w.y && verts[j].z == w.z) hit = j;
      if (hit < 0) return {};
      p.push_back(hit);
    }
    perms.push_back(std::move(p));
  }
  return perms;
}

std::vector<PlaneQ> ExtractPlanes(const std::vector<BigVecQ3> &verts,
                                  const std::vector<std::array<BigVecQ3, 3>> &view_domains);
std::vector<PlaneQ> FinishPlanes(const std::vector<std::pair<BigVecQ3, std::vector<int>>> &raw_planes,
                                 const std::vector<std::array<BigVecQ3, 3>> &view_domains);

// Exports rational vertices in Lean, C++, and JSON formats
void ExportRationalVertices(const std::vector<BigVecQ3> &verts, std::string_view base_name,
                            std::string_view model_name, int num_seeds) {
  const size_t n = verts.size();
  // 1. Export Lean 4 definition
  std::string lean_path = std::format("{}.lean", base_name);
  std::ofstream lean_out(lean_path);
  if (lean_out.good()) {
    lean_out << "/-!\n";
    lean_out << "Generated by codebdd.cc: the rational model of " << model_name << ".\n";
    if (num_seeds > 0) {
      lean_out << "Coordinates are multiples of 2^-52 (non-triangular faces snapped exactly planar),\n";
      lean_out << "within 6e-16 of the exact solid and strictly inside the unit sphere.\n";
    } else {
      lean_out << "The model file's exact rational vertices (strictly inside the unit sphere).\n";
    }
    lean_out << "scripts/update_vertices.py installs these rows into Vertices.lean.\n";
    lean_out << "-/\n\n";
    lean_out << "namespace Model\n\n";
    lean_out << "def rationalVertices : VertexIndex → Fin 3 → ℚ := ![\n";
    for (size_t i = 0; i < verts.size(); i++) {
      lean_out << std::format("  ![{}, {}, {}]{}\n",
                              FormatRat(verts[i].x),
                              FormatRat(verts[i].y),
                              FormatRat(verts[i].z),
                              (i + 1 < verts.size()) ? "," : "");
    }
    lean_out << "]\n\n";
    lean_out << "end Model\n";
    lean_out.close();
    Print("  Exported Lean 4 rational vertices to: " AGREEN("{}\n"), lean_path);
  }

  // 2. Export C++ header
  std::string h_path = std::format("{}.h", base_name);
  std::ofstream h_out(h_path);
  if (h_out.good()) {
    h_out << "// Generated by codebdd.cc: Best-possible rational vertices for " << model_name << ".\n";
    h_out << "#ifndef _NOPERT_MODEL_VERTICES_H\n";
    h_out << "#define _NOPERT_MODEL_VERTICES_H\n\n";
    h_out << "#include \"bignum/big.h\"\n";
    h_out << "#include \"bignum/big-vec.h\"\n\n";
    h_out << "inline constexpr int NUM_VERTICES_MODEL = " << n << ";\n\n";
    h_out << "// Whether these rationals are the solid itself (no C5 seeds: no rounded\n";
    h_out << "// model class around them), so the certificates need no model error terms\n";
    h_out << "// (tightVertexErrorQ = supportError = 0) and exact support ties are allowed.\n";
    h_out << "inline constexpr bool MODEL_EXACT = " << (num_seeds == 0 ? "true" : "false") << ";\n\n";
    h_out << "inline constexpr double VERTICES_MODEL[NUM_VERTICES_MODEL][3] = {\n";
    for (size_t i = 0; i < verts.size(); i++) {
      h_out << std::format("  {{ {: .17e}, {: .17e}, {: .17e} }}{}\n",
                           verts[i].x.ToDouble(),
                           verts[i].y.ToDouble(),
                           verts[i].z.ToDouble(),
                           (i + 1 < verts.size()) ? "," : "");
    }
    h_out << "};\n\n";
    h_out << "inline BigVecQ3 VertexQModel(size_t i) {\n";
    h_out << "  static const BigVecQ3 v[" << n << "] = {\n";
    for (size_t i = 0; i < verts.size(); i++) {
      auto [xn, xd] = verts[i].x.Parts();
      auto [yn, yd] = verts[i].y.Parts();
      auto [zn, zd] = verts[i].z.Parts();
      h_out << std::format("    BigVecQ3(BigRat(BigInt(\"{}\"), BigInt(\"{}\")), BigRat(BigInt(\"{}\"), BigInt(\"{}\")), BigRat(BigInt(\"{}\"), BigInt(\"{}\"))){}\n",
                           xn.ToString(), xd.ToString(),
                           yn.ToString(), yd.ToString(),
                           zn.ToString(), zd.ToString(),
                           (i + 1 < verts.size()) ? "," : "");
    }
    h_out << "  };\n";
    h_out << "  return v[i];\n";
    h_out << "}\n\n";
    h_out << "#endif\n";
    h_out.close();
    Print("  Exported C++ rational vertices to:     " AGREEN("{}\n"), h_path);
  }

  // 3. Export JSON summary
  std::string json_path = std::format("{}.json", base_name);
  std::ofstream j_out(json_path);
  if (j_out.good()) {
    j_out << "{\n";
    j_out << "  \"name\": \"" << model_name << " (best-possible exact rational export)\",\n";
    j_out << "  \"num_vertices\": " << verts.size() << ",\n";
    j_out << "  \"num_seeds\": " << num_seeds << ",\n";
    j_out << "  \"power_of_two_denominator\": true,\n";
    j_out << "  \"base_quantization_bits\": 52,\n";
    j_out << "  \"exact_quad_coplanarity\": true,\n";
    j_out << "  \"vertices\": [\n";
    for (size_t i = 0; i < verts.size(); i++) {
      j_out << std::format("    {{\"index\": {}, \"x\": \"{}\", \"y\": \"{}\", \"z\": \"{}\", \"double\": [{:.17g}, {:.17g}, {:.17g}]}}{}\n",
                           i,
                           FormatRat(verts[i].x),
                           FormatRat(verts[i].y),
                           FormatRat(verts[i].z),
                           verts[i].x.ToDouble(),
                           verts[i].y.ToDouble(),
                           verts[i].z.ToDouble(),
                           (i + 1 < verts.size()) ? "," : "");
    }
    j_out << "  ]\n";
    j_out << "}\n";
    j_out.close();
    Print("  Exported JSON rational vertices to:    " AGREEN("{}\n\n"), json_path);
  }
}

// Extract the facet planes of the model; crosses_view is relative to
// the view domain `view_corners_`.
std::vector<PlaneQ> ExtractPlanes(const std::vector<BigVecQ3> &verts,
                                  const std::vector<std::array<BigVecQ3, 3>> &view_corners_) {
  const size_t num_verts = verts.size();

  // Centroid
  BigVecQ3 centroid{BigRat(0), BigRat(0), BigRat(0)};
  for (const auto &v : verts) {
    centroid = centroid + v;
  }
  centroid = centroid / BigRat(num_verts);

  struct RawPlane {
    BigVecQ3 normal;
    BigRat d;
    std::vector<int> support;
  };
  std::vector<RawPlane> raw_planes;

  for (size_t i = 0; i < num_verts; i++) {
    for (size_t j = i + 1; j < num_verts; j++) {
      for (size_t k = j + 1; k < num_verts; k++) {
        BigVecQ3 e1 = verts[j] - verts[i];
        BigVecQ3 e2 = verts[k] - verts[i];
        BigVecQ3 n = BigVecQ3::Cross(e1, e2);
        if (n.x == 0 && n.y == 0 && n.z == 0) continue;

        BigRat d = BigVecQ3::Dot(n, verts[i]);
        int pos = 0, neg = 0;
        for (size_t m = 0; m < num_verts; m++) {
          BigRat val = BigVecQ3::Dot(n, verts[m]) - d;
          if (val > 0) pos++;
          else if (val < 0) neg++;
        }

        if (pos > 0 && neg > 0) continue; // strictly interior plane

        if (neg == 0) {
          n = BigVecQ3(-n.x, -n.y, -n.z);
          d = -d;
        }

        // Ensure outward orientation: centroid is inside, so n . centroid < d
        if (BigVecQ3::Dot(n, centroid) > d) {
          n = BigVecQ3(-n.x, -n.y, -n.z);
          d = -d;
        }

        // Check for duplicates
        bool duplicate = false;
        for (const auto &rp : raw_planes) {
          BigVecQ3 cx = BigVecQ3::Cross(n, rp.normal);
          if (cx.x == 0 && cx.y == 0 && cx.z == 0 && BigVecQ3::Dot(n, rp.normal) > 0) {
            duplicate = true;
            break;
          }
        }
        if (duplicate) continue;

        std::vector<int> support;
        for (size_t m = 0; m < num_verts; m++) {
          if (BigVecQ3::Dot(n, verts[m]) == d) {
            support.push_back(m);
          }
        }

        raw_planes.push_back(RawPlane{n, d, std::move(support)});
      }
    }
  }

  CHECK(raw_planes.size() >= 4) << "degenerate hull: " << raw_planes.size() << " facet planes";
  std::vector<std::pair<BigVecQ3, std::vector<int>>> normals;
  for (const auto &rp : raw_planes) normals.push_back({rp.normal, rp.support});
  return FinishPlanes(normals, view_corners_);
}

// Integer normals (coprime), sorted and indexed, with the view-domain flag.
std::vector<PlaneQ> FinishPlanes(const std::vector<std::pair<BigVecQ3, std::vector<int>>> &raw_planes,
                                 const std::vector<std::array<BigVecQ3, 3>> &view_domains) {
  std::vector<PlaneQ> planes;
  planes.reserve(raw_planes.size());

  for (const auto &[normal, support] : raw_planes) {
    struct { const BigVecQ3 &normal; const std::vector<int> &support; } rp{normal, support};
    auto [xn, xd] = rp.normal.x.Parts();
    auto [yn, yd] = rp.normal.y.Parts();
    auto [zn, zd] = rp.normal.z.Parts();

    // Multiply by common denominator
    BigInt ix = xn * yd * zd;
    BigInt iy = yn * xd * zd;
    BigInt iz = zn * xd * yd;

    BigInt g = BigInt::GCD(ix, BigInt::GCD(iy, iz));
    if (g > 1) {
      ix = ix / g;
      iy = iy / g;
      iz = iz / g;
    }

    PlaneQ pq;
    pq.int_x = ix;
    pq.int_y = iy;
    pq.int_z = iz;
    pq.normal = BigVecQ3(BigRat(ix), BigRat(iy), BigRat(iz));
    pq.face_vertices = rp.support;
    planes.push_back(pq);
  }

  // Canonical sort of planes
  std::sort(planes.begin(), planes.end(), [](const PlaneQ &a, const PlaneQ &b) {
    if (a.int_z != b.int_z) return a.int_z < b.int_z;
    if (a.int_y != b.int_y) return a.int_y < b.int_y;
    return a.int_x < b.int_x;
  });

  for (size_t idx = 0; idx < planes.size(); idx++) {
    planes[idx].index = idx;
  }

  // Check which planes cross (some triangle of) the view domain
  for (auto &p : planes) {
    for (const auto &tri : view_domains) {
      bool has_pos = false, has_neg = false;
      for (const auto &c : tri) {
        BigRat d = BigVecQ3::Dot(p.normal, c);
        if (d > 0) has_pos = true;
        if (d < 0) has_neg = true;
      }
      p.crosses_view = p.crosses_view || (has_pos && has_neg);
    }
  }

  return planes;
}

// The facet planes of the model's listed faces (--model_faces), for models
// whose rational vertices cannot make every face exactly planar: each
// face's outward normal from its exact vertices (the cross product of two
// diagonals, or of two edges for a triangle), rounded to a direction with
// integer components of ~60 bits. The codes are then sign vectors of these
// planes; the certificates never use faces.
std::vector<PlaneQ> PlanesFromModelFaces(const ModelFile &m,
                                         const std::vector<std::array<BigVecQ3, 3>> &view_corners_) {
  std::vector<std::pair<BigVecQ3, std::vector<int>>> raw;
  auto V = [&](int i) { return BigVecQ3(m.vertices[i][0], m.vertices[i][1], m.vertices[i][2]); };
  for (const auto &f : m.faces) {
    const int k = f.size();
    BigVecQ3 n = k >= 4 ? BigVecQ3::Cross(V(f[2]) - V(f[0]), V(f[3]) - V(f[1]))
                        : BigVecQ3::Cross(V(f[1]) - V(f[0]), V(f[2]) - V(f[0]));
    BigVecQ3 c{BigRat(0), BigRat(0), BigRat(0)};
    for (int v : f) c = c + V(v);
    if (BigVecQ3::Dot(n, c) < BigRat(0)) n = BigVecQ3(-n.x, -n.y, -n.z);
    const double mx = std::max({std::abs(n.x.ToDouble()), std::abs(n.y.ToDouble()), std::abs(n.z.ToDouble())});
    CHECK(mx > 0) << "degenerate face";
    const BigRat sc = BigRat::FromDouble(std::ldexp(1.0, 60) / mx);
    auto R = [&](const BigRat &x) { return BigRat(BigRat::Floor(x * sc + BigRat(1, 2))); };
    raw.push_back({BigVecQ3(R(n.x), R(n.y), R(n.z)), f});
  }
  return FinishPlanes(raw, view_corners_);
}

// Clip polygon with plane s * (normal . u) >= 0
ProjectivePoly ClipPolygon(const ProjectivePoly &poly, const HalfSpace &hs) {
  if (poly.IsEmpty()) return ProjectivePoly{};

  std::vector<BigVecQ3> out;
  const size_t n = poly.vertices.size();
  for (size_t i = 0; i < n; i++) {
    const BigVecQ3 &curr = poly.vertices[i];
    const BigVecQ3 &prev = poly.vertices[(i + n - 1) % n];

    BigRat d_curr = BigRat(hs.sign) * BigVecQ3::Dot(curr, hs.normal);
    BigRat d_prev = BigRat(hs.sign) * BigVecQ3::Dot(prev, hs.normal);

    if (d_curr >= 0) {
      if (d_prev < 0) {
        // Entering: intersection point I on segment prev -> curr
        // t = -d_prev / (d_curr - d_prev)
        // I = prev + t * (curr - prev) = (-d_prev * curr + d_curr * prev) / (d_curr - d_prev)
        BigRat denom = d_curr - d_prev;
        BigVecQ3 num = (curr * (-d_prev)) + (prev * d_curr);
        out.push_back(num / denom);
      }
      out.push_back(curr);
    } else if (d_prev >= 0) {
      // Leaving: intersection point I on segment prev -> curr
      // t = d_prev / (d_prev - d_curr)
      // I = prev + t * (curr - prev) = (-d_curr * prev + d_prev * curr) / (d_prev - d_curr)
      BigRat denom = d_prev - d_curr;
      BigVecQ3 num = (prev * (-d_curr)) + (curr * d_prev);
      out.push_back(num / denom);
    }
  }

  // Deduplicate consecutive vertices
  std::vector<BigVecQ3> cleaned;
  for (const auto &p : out) {
    if (cleaned.empty() || !(cleaned.back().x == p.x && cleaned.back().y == p.y && cleaned.back().z == p.z)) {
      cleaned.push_back(p);
    }
  }
  if (cleaned.size() > 1 && cleaned.front().x == cleaned.back().x &&
      cleaned.front().y == cleaned.back().y && cleaned.front().z == cleaned.back().z) {
    cleaned.pop_back();
  }

  if (cleaned.size() < 3) return ProjectivePoly{};

  // Check for non-zero area
  BigVecQ3 area_vec{BigRat(0), BigRat(0), BigRat(0)};
  for (size_t i = 1; i + 1 < cleaned.size(); i++) {
    BigVecQ3 e1 = cleaned[i] - cleaned[0];
    BigVecQ3 e2 = cleaned[i + 1] - cleaned[0];
    area_vec = area_vec + BigVecQ3::Cross(e1, e2);
  }
  if (area_vec.x == 0 && area_vec.y == 0 && area_vec.z == 0) {
    return ProjectivePoly{};
  }

  ProjectivePoly res;
  res.vertices = std::move(cleaned);
  res.boundary_planes = poly.boundary_planes;
  res.boundary_planes.push_back(hs);
  return res;
}

// Find a Farkas contradiction witness for an infeasible branch:
// Given active path constraints plus the new constraint hs,
// find a subset of <= 4 vectors that sum to 0 with strictly positive weights.
std::optional<FarkasWitness> FindFarkasWitness(
    const std::vector<HalfSpace> &active_planes,
    const HalfSpace &new_hs) {
  
  BigVecQ3 v_new = new_hs.normal * BigRat(new_hs.sign);

  // 1. Check if new_hs opposes any single plane: v_new + c * v_other = 0 (c > 0)
  for (const auto &hs : active_planes) {
    BigVecQ3 v = hs.normal * BigRat(hs.sign);
    BigVecQ3 cx = BigVecQ3::Cross(v_new, v);
    if (cx.x == 0 && cx.y == 0 && cx.z == 0) {
      BigRat dot = BigVecQ3::Dot(v_new, v);
      if (dot < 0) {
        FarkasWitness w;
        w.terms.push_back({new_hs.label, new_hs.plane_idx, new_hs.sign, v_new, BigRat(1)});
        BigRat lambda = -BigVecQ3::Dot(v_new, v_new) / dot;
        w.terms.push_back({hs.label, hs.plane_idx, hs.sign, v, lambda});
        return w;
      }
    }
  }

  // 2. Check 3-term coplanar combinations: l1 * v1 + l2 * v2 + 1 * v_new = 0 with l1, l2 > 0
  // Equivalently, -v_new = l1 * v1 + l2 * v2
  BigVecQ3 target = BigVecQ3(-v_new.x, -v_new.y, -v_new.z);
  const size_t m = active_planes.size();
  for (size_t i = 0; i < m; i++) {
    BigVecQ3 v1 = active_planes[i].normal * BigRat(active_planes[i].sign);
    for (size_t j = i + 1; j < m; j++) {
      BigVecQ3 v2 = active_planes[j].normal * BigRat(active_planes[j].sign);
      BigVecQ3 norm = BigVecQ3::Cross(v1, v2);
      if (norm.x == 0 && norm.y == 0 && norm.z == 0) continue;
      if (BigVecQ3::Dot(norm, target) == 0) {
        BigVecQ3 cx1 = BigVecQ3::Cross(target, v2);
        BigVecQ3 cx2 = BigVecQ3::Cross(v1, target);
        BigRat norm_sq = BigVecQ3::Dot(norm, norm);
        BigRat l1 = BigVecQ3::Dot(cx1, norm) / norm_sq;
        BigRat l2 = BigVecQ3::Dot(cx2, norm) / norm_sq;
        if (l1 > 0 && l2 > 0) {
          FarkasWitness w;
          w.terms.push_back({active_planes[i].label, active_planes[i].plane_idx, active_planes[i].sign, v1, l1});
          w.terms.push_back({active_planes[j].label, active_planes[j].plane_idx, active_planes[j].sign, v2, l2});
          w.terms.push_back({new_hs.label, new_hs.plane_idx, new_hs.sign, v_new, BigRat(1)});
          return w;
        }
      }
    }
  }

  // 3. Check 4-term non-coplanar combinations: l1 * v1 + l2 * v2 + l3 * v3 + l_new * v_new = 0
  for (size_t i = 0; i < m; i++) {
    BigVecQ3 v1 = active_planes[i].normal * BigRat(active_planes[i].sign);
    for (size_t j = i + 1; j < m; j++) {
      BigVecQ3 v2 = active_planes[j].normal * BigRat(active_planes[j].sign);
      for (size_t k = j + 1; k < m; k++) {
        BigVecQ3 v3 = active_planes[k].normal * BigRat(active_planes[k].sign);

        BigRat d0 = BigVecQ3::Det(v1, v2, v3);
        if (d0 == 0) continue;

        BigRat l1 = BigVecQ3::Det(v_new, v2, v3);
        BigRat l2 = BigVecQ3::Det(v1, v_new, v3);
        BigRat l3 = BigVecQ3::Det(v1, v2, v_new);
        BigRat l_new = -d0;

        // Check if all four weights have the same non-zero sign
        int s1 = BigRat::Sign(l1);
        int s2 = BigRat::Sign(l2);
        int s3 = BigRat::Sign(l3);
        int s4 = BigRat::Sign(l_new);

        if (s1 != 0 && s1 == s2 && s2 == s3 && s3 == s4) {
          BigRat mult = (s1 > 0) ? BigRat(1) : BigRat(-1);
          FarkasWitness w;
          w.terms.push_back({active_planes[i].label, active_planes[i].plane_idx, active_planes[i].sign, v1, l1 * mult});
          w.terms.push_back({active_planes[j].label, active_planes[j].plane_idx, active_planes[j].sign, v2, l2 * mult});
          w.terms.push_back({active_planes[k].label, active_planes[k].plane_idx, active_planes[k].sign, v3, l3 * mult});
          w.terms.push_back({new_hs.label, new_hs.plane_idx, new_hs.sign, v_new, l_new * mult});
          return w;
        }
      }
    }
  }

  // 3. Fallback: check triples of active planes summing to 0 without new_hs (should not happen if parent feasible)
  return std::nullopt;
}

// The vertices being partitioned (the model's, not the compiled-in ones), in
// double, for Compute2DHull. Set in main.
static std::vector<vec3> g_hull_vertices;

// Compute the static 2D convex hull vertex indices for a view inside this code cell
std::vector<int> Compute2DHull(const BigVecQ3 &interior_pt) {
  vec3 view_dir = {interior_pt.x.ToDouble(), interior_pt.y.ToDouble(), interior_pt.z.ToDouble()};
  view_dir = yocto::normalize(view_dir);

  // Pick an orthonormal 2D basis (x_proj, y_proj) perpendicular to view_dir
  vec3 up = (std::abs(view_dir.z) < 0.9) ? vec3{0, 0, 1} : vec3{0, 1, 0};
  vec3 x_axis = yocto::normalize(yocto::cross(view_dir, up));
  vec3 y_axis = yocto::cross(view_dir, x_axis);

  std::vector<vec2> pts2d;
  pts2d.reserve(g_hull_vertices.size());
  for (const vec3 &v : g_hull_vertices) {
    pts2d.push_back(vec2{yocto::dot(v, x_axis), yocto::dot(v, y_axis)});
  }

  return Hull2D::QuickHull(pts2d);
}

// Recursive BDD builder
std::unique_ptr<BDDNode> BuildBDD(
    const ProjectivePoly &poly,
    const std::vector<PlaneQ> &planes,
    size_t plane_idx,
    Code current_code,
    std::vector<HalfSpace> &active_path,
    std::vector<FeasibleCode> &feasible_codes) {

  if (plane_idx == planes.size()) {
    // Reached leaf: current_code exactly records the sign of every plane
    const Code final_code = current_code;

    auto leaf = std::make_unique<BDDNode>();
    leaf->type = BDDNode::FEASIBLE;
    leaf->code_val = final_code;
    leaf->code_hex = CodeHex(final_code, planes.size());

    FeasibleCode fc;
    fc.code_val = final_code;
    fc.hex_id = leaf->code_hex;
    fc.poly = poly;

    // Bit string (MSB to LSB: plane w-1 to plane 0; w = max(32, planes))
    const int width = std::max<int>(32, planes.size());
    fc.bit_string.resize(width);
    for (int b = 0; b < width; b++) {
      fc.bit_string[width - 1 - b] = final_code[b] ? '1' : '0';
    }

    // Fan triangulation
    for (size_t i = 1; i + 1 < poly.vertices.size(); i++) {
      fc.triangles.push_back({poly.vertices[0], poly.vertices[i], poly.vertices[i + 1]});
    }

    // Centroid of polygon for 2D hull evaluation
    BigVecQ3 centroid{BigRat(0), BigRat(0), BigRat(0)};
    for (const auto &v : poly.vertices) {
      centroid = centroid + v;
    }
    centroid = centroid / BigRat(poly.vertices.size());
    fc.hull_2d_vertices = Compute2DHull(centroid);

    feasible_codes.push_back(std::move(fc));
    return leaf;
  }

  const PlaneQ &plane = planes[plane_idx];

  // Test signs of vertices against this plane
  bool has_pos = false, has_neg = false;
  for (const auto &v : poly.vertices) {
    BigRat d = BigVecQ3::Dot(plane.normal, v);
    if (d > 0) has_pos = true;
    if (d < 0) has_neg = true;
  }

  if (!has_pos && !has_neg) {
    // Exactly on plane: arbitrarily assign to positive
    return BuildBDD(poly, planes, plane_idx + 1, WithBit(current_code, plane_idx), active_path, feasible_codes);
  }

  if (!has_neg) {
    // Entire polygon is >= 0
    auto node = std::make_unique<BDDNode>();
    node->type = BDDNode::BRANCH;
    node->plane_idx = plane_idx;

    // Neg branch is infeasible
    HalfSpace neg_hs{plane.index, -1, plane.normal, std::format("P{}-", plane.index)};
    auto neg_child = std::make_unique<BDDNode>();
    neg_child->type = BDDNode::INFEASIBLE;
    neg_child->witness = FindFarkasWitness(active_path, neg_hs);
    node->neg_child = std::move(neg_child);

    // Pos branch takes entire polygon
    active_path.push_back(HalfSpace{plane.index, +1, plane.normal, std::format("P{}+", plane.index)});
    node->pos_child = BuildBDD(poly, planes, plane_idx + 1, WithBit(current_code, plane_idx), active_path, feasible_codes);
    active_path.pop_back();

    return node;
  }

  if (!has_pos) {
    // Entire polygon is <= 0
    auto node = std::make_unique<BDDNode>();
    node->type = BDDNode::BRANCH;
    node->plane_idx = plane_idx;

    // Pos branch is infeasible
    HalfSpace pos_hs{plane.index, +1, plane.normal, std::format("P{}+", plane.index)};
    auto pos_child = std::make_unique<BDDNode>();
    pos_child->type = BDDNode::INFEASIBLE;
    pos_child->witness = FindFarkasWitness(active_path, pos_hs);
    node->pos_child = std::move(pos_child);

    // Neg branch takes entire polygon
    active_path.push_back(HalfSpace{plane.index, -1, plane.normal, std::format("P{}-", plane.index)});
    node->neg_child = BuildBDD(poly, planes, plane_idx + 1, current_code, active_path, feasible_codes);
    active_path.pop_back();

    return node;
  }

  // Polygon is split by plane
  HalfSpace neg_hs{plane.index, -1, plane.normal, std::format("P{}-", plane.index)};
  HalfSpace pos_hs{plane.index, +1, plane.normal, std::format("P{}+", plane.index)};

  ProjectivePoly poly_neg = ClipPolygon(poly, neg_hs);
  ProjectivePoly poly_pos = ClipPolygon(poly, pos_hs);

  auto node = std::make_unique<BDDNode>();
  node->type = BDDNode::BRANCH;
  node->plane_idx = plane_idx;

  // Neg branch
  if (poly_neg.IsEmpty()) {
    auto child = std::make_unique<BDDNode>();
    child->type = BDDNode::INFEASIBLE;
    child->witness = FindFarkasWitness(active_path, neg_hs);
    node->neg_child = std::move(child);
  } else {
    active_path.push_back(neg_hs);
    node->neg_child = BuildBDD(poly_neg, planes, plane_idx + 1, current_code, active_path, feasible_codes);
    active_path.pop_back();
  }

  // Pos branch
  if (poly_pos.IsEmpty()) {
    auto child = std::make_unique<BDDNode>();
    child->type = BDDNode::INFEASIBLE;
    child->witness = FindFarkasWitness(active_path, pos_hs);
    node->pos_child = std::move(child);
  } else {
    active_path.push_back(pos_hs);
    node->pos_child = BuildBDD(poly_pos, planes, plane_idx + 1, WithBit(current_code, plane_idx), active_path, feasible_codes);
    active_path.pop_back();
  }

  return node;
}

// One view triangle of the domain, its root and BDD; its codes are
// codes[first_code .. first_code + num_codes).
struct ViewDomain {
  int root = 0;
  ProjectivePoly poly;
  std::unique_ptr<BDDNode> tree;
  int first_code = 0, num_codes = 0;
};

// Write BDD and codes to JSON. With one view triangle the format is the
// original one ("fundamental_domain", "tree") plus the roots; with several,
// "view_domains" lists each one's root, corners, bounding planes, code range
// and tree instead.
void SerializeJSON(
    std::ostream &out,
    std::string_view model_name,
    const std::vector<BigVecQ3> &verts,
    const std::vector<PlaneQ> &planes,
    const std::vector<FeasibleCode> &codes,
    const std::vector<ViewDomain> &domains) {

  out << "{\n";
  out << "  \"polyhedron\": {\n";
  out << "    \"name\": \"" << model_name << "\",\n";
  out << "    \"num_vertices\": " << verts.size() << ",\n";
  out << "    \"vertices\": [\n";
  for (size_t i = 0; i < verts.size(); i++) {
    const auto &v = verts[i];
    out << std::format("      {{\"index\": {}, \"x\": \"{}\", \"y\": \"{}\", \"z\": \"{}\"}}{}\n",
                       i, FormatRat(v.x), FormatRat(v.y), FormatRat(v.z), (i + 1 < verts.size()) ? "," : "");
  }
  out << "    ]\n";
  out << "  },\n";

  // A view triangle's root, corners and bounding planes (indented by pad).
  auto DomainFields = [&](const ViewDomain &d, const std::string &pad) {
    out << pad << "\"name\": \"viewTriangle\",\n";
    out << pad << "\"root\": " << d.root << ",\n";
    out << pad << "\"corners\": [\n";
    for (int k = 0; k < 3; k++) {
      const BigVecQ3 &c = d.poly.vertices[k];
      out << pad << std::format("  {{\"x\": \"{}\", \"y\": \"{}\", \"z\": \"{}\"}}{}\n", FormatRat(c.x),
                                FormatRat(c.y), FormatRat(c.z), k < 2 ? "," : "");
    }
    out << pad << "],\n";
    out << pad << "\"bounding_planes\": [\n";
    for (int k = 0; k < 3; k++) {
      const HalfSpace &h = d.poly.boundary_planes[k];
      out << pad << std::format("  {{\"label\": \"{}\", \"normal\": [\"{}\", \"{}\", \"{}\"]}}{}\n", h.label,
                                FormatRat(h.normal.x), FormatRat(h.normal.y), FormatRat(h.normal.z),
                                k < 2 ? "," : "");
    }
    out << pad << "]";
  };
  if (domains.size() == 1) {
    out << "  \"fundamental_domain\": {\n";
    DomainFields(domains[0], "    ");
    out << "\n  },\n";
  }

  out << "  \"num_planes\": " << planes.size() << ",\n";
  out << "  \"planes\": [\n";
  for (size_t i = 0; i < planes.size(); i++) {
    const auto &p = planes[i];
    out << "    {\n";
    out << "      \"index\": " << p.index << ",\n";
    out << std::format("      \"normal_int\": [{}, {}, {}],\n", p.int_x.ToString(), p.int_y.ToString(), p.int_z.ToString());
    out << "      \"crosses_view\": " << (p.crosses_view ? "true" : "false") << ",\n";
    out << "      \"face_vertices\": [";
    for (size_t j = 0; j < p.face_vertices.size(); j++) {
      out << p.face_vertices[j] << (j + 1 < p.face_vertices.size() ? ", " : "");
    }
    out << "]\n";
    out << "    }" << (i + 1 < planes.size() ? "," : "") << "\n";
  }
  out << "  ],\n";

  out << "  \"num_codes\": " << codes.size() << ",\n";
  out << "  \"codes\": [\n";
  for (size_t i = 0; i < codes.size(); i++) {
    const auto &c = codes[i];
    out << "    {\n";
    out << "      \"code_hex\": \"" << c.hex_id << "\",\n";
    out << "      \"root\": " << c.root << ",\n";
    if (planes.size() <= 32) out << "      \"code_uint32\": " << c.code_val.to_ullong() << ",\n";
    out << "      \"bit_string\": \"" << c.bit_string << "\",\n";
    out << "      \"num_polygon_vertices\": " << c.poly.vertices.size() << ",\n";
    out << "      \"polygon_vertices\": [\n";
    for (size_t j = 0; j < c.poly.vertices.size(); j++) {
      const auto &v = c.poly.vertices[j];
      out << std::format("        {{\"x\": \"{}\", \"y\": \"{}\", \"z\": \"{}\"}}{}\n",
                         v.x.ToString(), v.y.ToString(), v.z.ToString(), (j + 1 < c.poly.vertices.size()) ? "," : "");
    }
    out << "      ],\n";
    out << "      \"num_triangles\": " << c.triangles.size() << ",\n";
    out << "      \"triangles\": [\n";
    for (size_t t = 0; t < c.triangles.size(); t++) {
      const auto &tri = c.triangles[t];
      out << "        [\n";
      for (int k = 0; k < 3; k++) {
        out << std::format("          {{\"x\": \"{}\", \"y\": \"{}\", \"z\": \"{}\"}}{}\n",
                           tri[k].x.ToString(), tri[k].y.ToString(), tri[k].z.ToString(), (k < 2) ? "," : "");
      }
      out << "        ]" << (t + 1 < c.triangles.size() ? "," : "") << "\n";
    }
    out << "      ],\n";
    out << "      \"hull_2d_vertices\": [";
    for (size_t h = 0; h < c.hull_2d_vertices.size(); h++) {
      out << c.hull_2d_vertices[h] << (h + 1 < c.hull_2d_vertices.size() ? ", " : "");
    }
    out << "]\n";
    out << "    }" << (i + 1 < codes.size() ? "," : "") << "\n";
  }
  out << "  ],\n";

  // Lambda to serialize tree recursively
  auto SerializeNode = [&](auto &self, const BDDNode *node, int indent) -> void {
    std::string pad(indent, ' ');
    if (node->type == BDDNode::FEASIBLE) {
      out << pad << "{\n";
      out << pad << "  \"type\": \"feasible\",\n";
      if (planes.size() <= 32) {
        out << pad << "  \"code_hex\": \"" << node->code_hex << "\",\n";
        out << pad << "  \"code_uint32\": " << node->code_val.to_ullong() << "\n";
      } else {
        out << pad << "  \"code_hex\": \"" << node->code_hex << "\"\n";
      }
      out << pad << "}";
    } else if (node->type == BDDNode::INFEASIBLE) {
      out << pad << "{\n";
      out << pad << "  \"type\": \"infeasible\"";
      if (node->witness.has_value()) {
        out << ",\n" << pad << "  \"witness\": [\n";
        const auto &terms = node->witness->terms;
        for (size_t t = 0; t < terms.size(); t++) {
          out << pad << "    {\n";
          out << pad << "      \"label\": \"" << terms[t].label << "\",\n";
          out << pad << "      \"plane_idx\": " << terms[t].plane_idx << ",\n";
          out << pad << "      \"sign\": " << terms[t].sign << ",\n";
          out << pad << "      \"lambda\": \"" << terms[t].lambda.ToString() << "\"\n";
          out << pad << "    }" << (t + 1 < terms.size() ? "," : "") << "\n";
        }
        out << pad << "  ]\n";
      } else {
        out << "\n";
      }
      out << pad << "}";
    } else {
      out << pad << "{\n";
      out << pad << "  \"type\": \"branch\",\n";
      out << pad << "  \"plane_idx\": " << node->plane_idx << ",\n";
      out << pad << "  \"neg\":\n";
      self(self, node->neg_child.get(), indent + 4);
      out << ",\n";
      out << pad << "  \"pos\":\n";
      self(self, node->pos_child.get(), indent + 4);
      out << "\n" << pad << "}";
    }
  };

  if (domains.size() == 1) {
    out << "  \"tree\":\n";
    SerializeNode(SerializeNode, domains[0].tree.get(), 4);
  } else {
    out << "  \"view_domains\": [\n";
    for (size_t k = 0; k < domains.size(); k++) {
      out << "    {\n";
      DomainFields(domains[k], "      ");
      out << ",\n      \"first_code\": " << domains[k].first_code << ",\n";
      out << "      \"num_codes\": " << domains[k].num_codes << ",\n";
      out << "      \"tree\":\n";
      SerializeNode(SerializeNode, domains[k].tree.get(), 8);
      out << "\n    }" << (k + 1 < domains.size() ? "," : "") << "\n";
    }
    out << "  ]";
  }
  out << "\n}\n";
}

int main(int argc, char **argv) {
  Timer timer;
  Print(AWHITE("================================================================\n"));
  Print(ACYAN("  Code subdivision & BDD generator\n"));
  Print(AWHITE("================================================================\n\n"));

  bool export_only = false;
  std::string output_path = "codebdd.json";
  std::string export_prefix = "model_vertices";
  std::string model_file = "septopert_model.txt";
  bool model_faces = false;

  for (int i = 1; i < argc; i++) {
    std::string_view arg = argv[i];
    if (arg == "--export_rational" || arg == "--export") {
      export_only = true;
    } else if (arg.starts_with("--output=")) {
      output_path = arg.substr(9);
    } else if (arg.starts_with("--model_file=")) {
      model_file = arg.substr(13);
    } else if (arg == "--model_faces") {
      model_faces = true;
    } else if (arg.starts_with("--export_prefix=")) {
      export_prefix = arg.substr(16);
    } else if (arg.starts_with("-")) {
      Print(ARED("Unknown flag: {}\n"), arg);
      return 1;
    } else {
      output_path = std::string(arg);
    }
  }

  // The model: rounding, planarization and Lean's tightVertex bound (see
  // ModelRationalVertices). Try scales until the rational vertices are
  // comfortably within the 4e-16 bound (target 3.6e-16).
  const ModelFile model = LoadModelFile(model_file);
  const std::string model_name = model.name;
  CHECK(!model.view_triangles.empty()) << model_file << ": no view_triangle";
  const std::vector<std::array<BigVecQ3, 3>> &view_corners = model.view_triangles;
  std::vector<BigVecQ3> verts;
  const BigRat target = BigRat(36, 100000000000000000LL) * BigRat(36, 100000000000000000LL);
  if (model.seeds == 0) {
    // No C5 structure: the rational vertices are the model (exactly C3v, checked).
    verts = model.rational_vertices;
    const auto perms = C3vVertexPermutations(verts);
    CHECK(!perms.empty()) << "the rational vertices are not invariant under the coordinate permutations";
    static const char *kNames[5] = {"c3Mat 1", "c3Mat 2", "mirrorMat 0", "mirrorMat 1", "mirrorMat 2"};
    Print("Rational vertices from the model file (no C5 seeds): exactly C3v about (1,1,1)\n");
    for (int g = 0; g < 5; g++) {
      std::string p;
      for (int v : perms[g]) p += std::format(" {}", v);
      Print("  {:12} permutes the vertices as [{} ]\n", kNames[g], p);
    }
    BigRat worst(0);
    for (size_t i = 0; i < verts.size(); i++) {
      const BigRat dx = verts[i].x - model.vertices[i][0], dy = verts[i].y - model.vertices[i][1],
                   dz = verts[i].z - model.vertices[i][2];
      worst = std::max(worst, dx * dx + dy * dy + dz * dz);
      CHECK(BigVecQ3::Dot(verts[i], verts[i]) < BigRat(1)) << "vertex " << i << " has norm >= 1";
    }
    Print("  Max distance from the decimal vertices: {:.3e}\n", std::sqrt(worst.ToDouble()));
    CHECK(worst <= BigRat(36, 100000000000000000LL) * BigRat(1, 100000000000000LL))
        << "rational vertices more than 6e-16 from the vertex lines";
  } else if (!model.rational_vertices.empty()) {
    verts = model.rational_vertices;
    const BigRat d2 = TightVertexDistanceSq(verts);
    Print("Rational vertices from the model file: max |rational - tight| = {:.3e} (Lean bound 4e-16)\n",
          std::sqrt(d2.ToDouble()));
    CHECK(d2 <= target) << "the model file's rational vertices are not within the tightVertex bound";
    BigRat worst(0);
    for (size_t i = 0; i < verts.size(); i++) {
      const BigRat dx = verts[i].x - model.vertices[i][0], dy = verts[i].y - model.vertices[i][1],
                   dz = verts[i].z - model.vertices[i][2];
      worst = std::max(worst, dx * dx + dy * dy + dz * dz);
    }
    Print("  Max distance from the exact model: {:.3e} (budget 6e-16)\n", std::sqrt(worst.ToDouble()));
    CHECK(worst <= BigRat(36, 100000000000000000LL) * BigRat(1, 100000000000000LL))
        << "rational vertices more than 6e-16 from the exact model";
  }
  for (int attempt = 0; verts.empty(); attempt++) {
    CHECK(attempt < 1000) << "No scale found within the tightVertex bound";
    auto v = ModelRationalVertices(model, attempt, false);
    const BigRat d2 = TightVertexDistanceSq(v);
    if (d2 <= target) {
      Print("Scale attempt {}: max |rational - tight| = {:.3e} (Lean bound 4e-16)\n",
            attempt, std::sqrt(d2.ToDouble()));
      verts = ModelRationalVertices(model, attempt, true);
      break;
    }
  }

  // Always export rational representations in Lean 4, C++, and JSON formats
  ExportRationalVertices(verts, export_prefix, model_name, model.seeds);

  if (export_only) {
    Print("\n" AGREEN("Rational vertices exported successfully.") " Exiting (--export_rational).\n");
    return 0;
  }

  Print("Extracting facet planes from vertices...\n");
  std::vector<PlaneQ> planes = model_faces ? PlanesFromModelFaces(model, view_corners)
                                            : ExtractPlanes(verts, view_corners);
  for (const auto &v : verts) g_hull_vertices.push_back(vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()});
  Print("Found " AGREEN("{}") " facet planes.\n", planes.size());

  int crossing_count = 0;
  for (const auto &p : planes) {
    if (p.crosses_view) crossing_count++;
  }
  Print("Planes crossing the view domain: " ACYAN("{}") " (constant sign: {})\n\n",
        crossing_count, planes.size() - crossing_count);

  // Each view triangle is partitioned separately; its codes follow the
  // previous triangles' (a code cell meeting two triangles appears in both).
  // Initial root polygon: the view triangle. Edge k is opposite corner k:
  // normal cross(c_{k+1}, c_{k+2}), oriented so that corner k is on the
  // positive side. (The triangle is on its root's plane, so a positive
  // multiple of each view: the signs u . n are the codes.)
  std::vector<FeasibleCode> feasible_codes;
  std::vector<ViewDomain> domains;
  CHECK((int)planes.size() <= kMaxPlanes) << planes.size() << " planes";
  for (const auto &corners : view_corners) {
    ViewDomain dom;
    dom.root = TriangleRoot(corners);
    ProjectivePoly &root_poly = dom.poly;
    root_poly.vertices = {corners[0], corners[1], corners[2]};
    for (int k = 0; k < 3; k++) {
      BigVecQ3 n = BigVecQ3::Cross(corners[(k + 1) % 3], corners[(k + 2) % 3]);
      if (BigVecQ3::Dot(n, corners[k]) < BigRat(0)) n = BigVecQ3(-n.x, -n.y, -n.z);
      CHECK(BigVecQ3::Dot(n, corners[k]) > BigRat(0)) << "degenerate view triangle";
      root_poly.boundary_planes.push_back({-1, +1, n, std::format("W{}", k)});
    }
    std::vector<HalfSpace> active_path = root_poly.boundary_planes;
    Print("Recursively partitioning view triangle {} (root {}) into BDD...\n", domains.size(), dom.root);
    dom.first_code = feasible_codes.size();
    dom.tree = BuildBDD(root_poly, planes, 0, Code(), active_path, feasible_codes);
    dom.num_codes = feasible_codes.size() - dom.first_code;
    for (int c = dom.first_code; c < (int)feasible_codes.size(); c++) feasible_codes[c].root = dom.root;
    Print("  {} codes\n", dom.num_codes);
    domains.push_back(std::move(dom));
  }

  Print("\n" AGREEN("SUCCESS!") " Discovered " ACYAN("{}") " non-empty codes in the view domain.\n",
        feasible_codes.size());

  size_t total_triangles = 0;
  std::map<size_t, int> hull_size_counts;
  for (const auto &fc : feasible_codes) {
    total_triangles += fc.triangles.size();
    hull_size_counts[fc.hull_2d_vertices.size()]++;
  }
  Print("Total projective triangles covering the view triangle: " ACYAN("{}") " (avg {:.2f}/code)\n",
        total_triangles, (double)total_triangles / feasible_codes.size());

  Print("\n2D Hull vertex count distribution across codes:\n");
  for (const auto &[hull_sz, count] : hull_size_counts) {
    Print("  {} vertices: {} codes\n", hull_sz, count);
  }

  Print("\nWriting BDD and code database to " AYELLOW("{}") "...\n", output_path);
  std::ofstream out(output_path);
  CHECK(out.good()) << "Failed to open " << output_path << " for writing";
  SerializeJSON(out, model_name, verts, planes, feasible_codes, domains);
  out.close();

  Print("Finished in " AGREEN("{}\n\n"), ANSI::Time(timer.Seconds()));
  return 0;
}
