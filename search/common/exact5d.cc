#include "exact5d.h"

#include "solid.h"

#include <array>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "model.h"

namespace exact5d {

namespace {

VecQ Vertex(int k) {
  const BigVecQ3 &v = VertexQ(k);
  return {v.x, v.y, v.z};
}

VecQ Sub(const VecQ &a, const VecQ &b) {
  return {a[0] - b[0], a[1] - b[1], a[2] - b[2]};
}

VecQ Add(const VecQ &a, const VecQ &b) {
  return {a[0] + b[0], a[1] + b[1], a[2] + b[2]};
}

VecQ Scale(const Q &s, const VecQ &a) {
  return {s * a[0], s * a[1], s * a[2]};
}

// LocalCertificate.crossQ
VecQ Cross(const VecQ &u, const VecQ &v) {
  return {u[1] * v[2] - u[2] * v[1],
          u[2] * v[0] - u[0] * v[2],
          u[0] * v[1] - u[1] * v[0]};
}

// AtlasProjectiveEdgeCertificate.dotQ
Q Dot(const VecQ &a, const VecQ &b) {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}

// SnubCube.ProjectiveView.midpoint
VecQ Midpoint(const VecQ &a, const VecQ &b) {
  const Q two(2);
  return {(a[0] + b[0]) / two, (a[1] + b[1]) / two, (a[2] + b[2]) / two};
}

Q Max3(const Q &a, const Q &b, const Q &c) { return BigRat::Max(a, BigRat::Max(b, c)); }
Q Min3(const Q &a, const Q &b, const Q &c) { return BigRat::Min(a, BigRat::Min(b, c)); }

// AtlasProjectiveLocalCertificate.AxisCertificate.mixQ
Q MixQ(const AxisCertificate &cert, int i) { return Q(cert.mix[i], 1000); }

// SnubCube.ProjectiveLocalCertificate.mulLinear
Quad3 MulLinear(const VecQ &a, const VecQ &b) {
  Quad3 q;
  q.cxx = a[0] * b[0];
  q.cxy = a[0] * b[1] + a[1] * b[0];
  q.cxz = a[0] * b[2] + a[2] * b[0];
  q.cyy = a[1] * b[1];
  q.cyz = a[1] * b[2] + a[2] * b[1];
  q.czz = a[2] * b[2];
  return q;
}

Quad3 Monomial(int which) {
  Quad3 q;
  switch (which) {
  case 0: q.c0 = Q(1); break;
  case 1: q.cx = Q(1); break;
  case 2: q.cy = Q(1); break;
  case 3: q.cz = Q(1); break;
  case 4: q.cxx = Q(1); break;
  case 5: q.cxy = Q(1); break;
  case 6: q.cxz = Q(1); break;
  case 7: q.cyy = Q(1); break;
  case 8: q.cyz = Q(1); break;
  case 9: q.czz = Q(1); break;
  }
  return q;
}

// SnubCube.CayleyEdgeCertificate.{denomQuadratic, numeratorQuadratic}
Quad3 DenomQuadratic() {
  return QuadAdd(QuadAdd(QuadAdd(Monomial(0), Monomial(4)), Monomial(7)), Monomial(9));
}

Quad3 NumeratorQuadratic(int c, int j) {
  const Quad3 one = Monomial(0), x = Monomial(1), y = Monomial(2), z = Monomial(3);
  const Quad3 xx = Monomial(4), xy = Monomial(5), xz = Monomial(6);
  const Quad3 yy = Monomial(7), yz = Monomial(8), zz = Monomial(9);
  const Q two(2);
  switch (c * 3 + j) {
  case 0: return QuadSub(QuadSub(QuadAdd(one, xx), yy), zz);
  case 1: return QuadScale(two, QuadSub(xy, z));
  case 2: return QuadScale(two, QuadAdd(xz, y));
  case 3: return QuadScale(two, QuadAdd(xy, z));
  case 4: return QuadSub(QuadAdd(QuadSub(one, xx), yy), zz);
  case 5: return QuadScale(two, QuadSub(yz, x));
  case 6: return QuadScale(two, QuadSub(xz, y));
  case 7: return QuadScale(two, QuadAdd(yz, x));
  case 8: return QuadAdd(QuadSub(QuadSub(one, xx), yy), zz);
  }
  LOG(FATAL) << "bad index";
  return {};
}

// AtlasQuadratic.chartSign
Q ChartSign(int chart, int c) {
  return (chart == 0 || chart == c + 1) ? Q(1) : Q(-1);
}

// AtlasQuadratic.displacementQuadratic
Quad3 DisplacementQuadratic(int chart, int inner, int outer, int c) {
  const VecQ vin = Vertex(inner), vout = Vertex(outer);
  Quad3 sum;
  for (int j = 0; j < 3; j++) {
    sum = QuadAdd(sum, QuadScale(vin[j], QuadScale(ChartSign(chart, c), NumeratorQuadratic(c, j))));
  }
  return QuadSub(sum, QuadScale(vout[c], DenomQuadratic()));
}

// Box.localShell.triangleBalls
std::array<RatBall, 3> TriangleBalls(const TriangleQ &tri) {
  std::array<RatBall, 3> balls;
  for (int c = 0; c < 3; c++) {
    balls[c] = BallOfEndpoints(Min3(tri[0][c], tri[1][c], tri[2][c]),
                               Max3(tri[0][c], tri[1][c], tri[2][c]));
  }
  return balls;
}

// Box.relativeBalls: the Cayley coordinates x, y, z.
std::array<RatBall, 3> RelativeBalls(const Interval5 &iv) {
  return {BallOfEndpoints(iv.min[2], iv.max[2]),
          BallOfEndpoints(iv.min[3], iv.max[3]),
          BallOfEndpoints(iv.min[4], iv.max[4])};
}

// AtlasProjectiveLocalCertificate.Box.exactSupportTie
bool ExactSupportTie(const AxisCertificate &cert, int i, int k) {
  const int s = cert.index[i];
  return k == s ||
         (cert.mix[i] == 1000 && s == cert.edge_finish[i] && k == cert.edge_start[i]) ||
         (cert.mix[i] == 0 && s == cert.edge_start2[i] && k == cert.edge_finish2[i]);
}

// AtlasEdgeCertificate.endpointAbsBound
Q EndpointAbsBound(const Q &lo, const Q &hi) {
  return BigRat::Max(BigRat::Abs(lo), BigRat::Abs(hi));
}

}  // namespace

RatBall BallConst(const Q &q) { return {q, Q(0)}; }
RatBall BallAdd(const RatBall &a, const RatBall &b) {
  return {a.center + b.center, a.radius + b.radius};
}
RatBall BallNeg(const RatBall &a) { return {-a.center, a.radius}; }
RatBall BallSub(const RatBall &a, const RatBall &b) { return BallAdd(a, BallNeg(b)); }
RatBall BallMul(const RatBall &a, const RatBall &b) {
  return {a.center * b.center,
          BigRat::Abs(a.center) * b.radius + a.radius * BigRat::Abs(b.center) +
              a.radius * b.radius};
}
RatBall BallOfEndpoints(const Q &lo, const Q &hi) {
  return {(lo + hi) / Q(2), (hi - lo) / Q(2)};
}

Quad3 QuadAdd(const Quad3 &a, const Quad3 &b) {
  return {a.c0 + b.c0, a.cx + b.cx, a.cy + b.cy, a.cz + b.cz, a.cxx + b.cxx,
          a.cxy + b.cxy, a.cxz + b.cxz, a.cyy + b.cyy, a.cyz + b.cyz, a.czz + b.czz};
}
Quad3 QuadSub(const Quad3 &a, const Quad3 &b) {
  return {a.c0 - b.c0, a.cx - b.cx, a.cy - b.cy, a.cz - b.cz, a.cxx - b.cxx,
          a.cxy - b.cxy, a.cxz - b.cxz, a.cyy - b.cyy, a.cyz - b.cyz, a.czz - b.czz};
}
Quad3 QuadScale(const Q &s, const Quad3 &a) {
  return {s * a.c0, s * a.cx, s * a.cy, s * a.cz, s * a.cxx,
          s * a.cxy, s * a.cxz, s * a.cyy, s * a.cyz, s * a.czz};
}
Q QuadEvalQ(const Quad3 &q, const Q &x, const Q &y, const Q &z) {
  return q.c0 + q.cx * x + q.cy * y + q.cz * z + q.cxx * x * x +
         q.cxy * x * y + q.cxz * x * z + q.cyy * y * y + q.cyz * y * z + q.czz * z * z;
}

// RatQuadratic3.evalBall = RatPolynomial.evalBall of centeredPolynomial. Each
// centered variable (v - c) evaluates to the ball (0, r) and constants have
// radius 0, so the tree evaluates exactly to center Q(c) and radius
// sum |g_i| r_i + sum |c_ij| r_i r_j (g = gradient at the center).
RatBall QuadEvalBall(const std::array<RatBall, 3> &vars, const Quad3 &q) {
  const Q &x = vars[0].center, &y = vars[1].center, &z = vars[2].center;
  const Q &rx = vars[0].radius, &ry = vars[1].radius, &rz = vars[2].radius;
  const Q two(2);
  const Q gx = q.cx + two * q.cxx * x + q.cxy * y + q.cxz * z;
  const Q gy = q.cy + q.cxy * x + two * q.cyy * y + q.cyz * z;
  const Q gz = q.cz + q.cxz * x + q.cyz * y + two * q.czz * z;
  auto A = [](const Q &v) { return BigRat::Abs(v); };
  Q radius = A(gx) * rx + A(gy) * ry + A(gz) * rz +
             A(q.cxx) * (rx * rx) + A(q.cxy) * (rx * ry) + A(q.cxz) * (rx * rz) +
             A(q.cyy) * (ry * ry) + A(q.cyz) * (ry * rz) + A(q.czz) * (rz * rz);
  return {QuadEvalQ(q, x, y, z), radius};
}

// QuadraticBernstein.coefficient and lower.
Q BernsteinLower(const std::array<RatBall, 3> &vars, const Quad3 &q) {
  const Q two(2);
  const Q lx = vars[0].center - vars[0].radius;
  const Q ly = vars[1].center - vars[1].radius;
  const Q lz = vars[2].center - vars[2].radius;
  const Q wx = two * vars[0].radius, wy = two * vars[1].radius, wz = two * vars[2].radius;
  const Q a0 = QuadEvalQ(q, lx, ly, lz);
  const Q ax = wx * (q.cx + two * q.cxx * lx + q.cxy * ly + q.cxz * lz);
  const Q ay = wy * (q.cy + q.cxy * lx + two * q.cyy * ly + q.cyz * lz);
  const Q az = wz * (q.cz + q.cxz * lx + q.cyz * ly + two * q.czz * lz);
  const Q axx = q.cxx * wx * wx, ayy = q.cyy * wy * wy, azz = q.czz * wz * wz;
  const Q axy = q.cxy * wx * wy, axz = q.cxz * wx * wz, ayz = q.cyz * wy * wz;
  Q best;
  bool first = true;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      for (int k = 0; k < 3; k++) {
        const Q u(i, 2), v(j, 2), w(k, 2);
        Q coeff = a0 + u * ax + v * ay + w * az;
        if (i == 2) coeff = coeff + axx;
        if (j == 2) coeff = coeff + ayy;
        if (k == 2) coeff = coeff + azz;
        coeff = coeff + u * v * axy + u * w * axz + v * w * ayz;
        if (first || coeff < best) best = coeff;
        first = false;
      }
    }
  }
  return best;
}

// (0 for an exact model, solid::kModelExact: the solid is the rational model.)
Q TightVertexErrorQ() { return solid::kModelExact ? Q(0) : Q(6, 10000000000000000LL); }
Q SupportError() { return Q(10) * TightVertexErrorQ(); }

VecQ EdgeQ(const AxisCertificate &cert, int i) {
  const Q m = MixQ(cert, i);
  return Add(Scale(m, Sub(Vertex(cert.edge_start[i]), Vertex(cert.edge_finish[i]))),
             Scale(Q(1) - m, Sub(Vertex(cert.edge_start2[i]), Vertex(cert.edge_finish2[i]))));
}

VecQ WeightCoefficient(const AxisCertificate &cert, int i) {
  const int a = (i + 1) % 3, b = (i + 2) % 3;
  return Cross(EdgeQ(cert, a), EdgeQ(cert, b));
}

namespace {

// The subexpressions shared by a box's checks, each computed once (the Lean
// definitions recompute them; the values are identical).
struct Pre {
  std::array<VecQ, 3> edge;   // Box.certificate.edgeQ i
  std::array<VecQ, 3> wcoef;  // weightCoefficient i
  // localShell.supportAt 0 corner i k, as [corner][i][k].
  std::array<std::array<std::vector<Q>, 3>, 3> support_at;
  // localShell.weightAt 0 corner i, as [corner][i].
  std::array<std::array<Q, 3>, 3> weight_at;
  // Box.contactQuadratic i c, as [i][c].
  std::array<std::array<Quad3, 3>, 3> contact;
};

Pre Precompute(const GlobalBox &box) {
  Pre p;
  const AxisCertificate &cert = box.certificate;
  for (int i = 0; i < 3; i++) p.edge[i] = EdgeQ(cert, i);
  for (int i = 0; i < 3; i++) p.wcoef[i] = Cross(p.edge[(i + 1) % 3], p.edge[(i + 2) % 3]);
  for (int i = 0; i < 3; i++) {
    const VecQ vs = Vertex(cert.index[i]);
    std::vector<VecQ> cross(NUM_VERTICES);
    for (int k = 0; k < NUM_VERTICES; k++) cross[k] = Cross(p.edge[i], Sub(Vertex(k), vs));
    for (int corner = 0; corner < 3; corner++) {
      p.support_at[corner][i].resize(NUM_VERTICES);
      for (int k = 0; k < NUM_VERTICES; k++) {
        p.support_at[corner][i][k] = Dot(box.triangle[corner], cross[k]);
      }
      p.weight_at[corner][i] = Dot(box.triangle[corner], p.wcoef[i]);
    }
    std::array<Quad3, 3> d;
    for (int c = 0; c < 3; c++) {
      d[c] = DisplacementQuadratic(box.chart, box.inner_index[i], cert.index[i], c);
    }
    const VecQ &e = p.edge[i];
    p.contact[i][0] = QuadSub(QuadScale(e[1], d[2]), QuadScale(e[2], d[1]));
    p.contact[i][1] = QuadSub(QuadScale(e[2], d[0]), QuadScale(e[0], d[2]));
    p.contact[i][2] = QuadSub(QuadScale(e[0], d[1]), QuadScale(e[1], d[0]));
  }
  return p;
}

Q SupportUpperP(const GlobalBox &box, const Pre &p, int i, int k) {
  if (ExactSupportTie(box.certificate, i, k)) return Q(0);
  return Max3(p.support_at[0][i][k], p.support_at[1][i][k], p.support_at[2][i][k]) + SupportError();
}

Q WeightLowerP(const Pre &p, int i) {
  return Min3(p.weight_at[0][i], p.weight_at[1][i], p.weight_at[2][i]) - SupportError();
}

Q WeightUpperP(const Pre &p, int i) {
  return Max3(p.weight_at[0][i], p.weight_at[1][i], p.weight_at[2][i]) + SupportError();
}

// Box.weightedSupportControl / weightedSupportUpper / contactDefectUpper /
// weightedDefectUpper.
Q WeightedDefectUpperP(const GlobalBox &box, const Pre &p) {
  const Q se = SupportError();
  Q total(0);
  for (int i = 0; i < 3; i++) {
    std::array<Q, 3> w;
    for (int a = 0; a < 3; a++) w[a] = p.weight_at[a][i] + se;
    Q contact(0);  // max 0 (max over k ...)
    for (int k = 0; k < NUM_VERTICES; k++) {
      Q upper(0);
      if (k != box.certificate.index[i]) {
        std::array<Q, 3> sv;
        for (int a = 0; a < 3; a++) sv[a] = p.support_at[a][i][k] + se;
        bool first = true;
        for (int a = 0; a < 3; a++) {
          for (int b = 0; b < 3; b++) {
            const Q control = (w[a] * sv[b] + w[b] * sv[a]) / Q(2);
            if (first || control > upper) upper = control;
            first = false;
          }
        }
      }
      contact = BigRat::Max(contact, upper);
    }
    total = total + contact;
  }
  return total;
}

// Box.adjustedViewDisplacementQuadratic at view n.
Quad3 AdjustedViewDisplacementQuadraticP(const GlobalBox &box, const Pre &p, const VecQ &n) {
  Quad3 disp;
  for (int i = 0; i < 3; i++) {
    const Q w = Dot(n, p.wcoef[i]);  // Box.weightQ
    Quad3 contact;                    // Box.viewContactQuadratic
    for (int c = 0; c < 3; c++) contact = QuadAdd(contact, QuadScale(n[c], p.contact[i][c]));
    disp = QuadAdd(disp, QuadScale(w, contact));
  }
  // Box.cayleyConstraintQuadratic = x² + y² + z² - 3
  Quad3 constraint;
  constraint.c0 = Q(-3);
  constraint.cxx = Q(1);
  constraint.cyy = Q(1);
  constraint.czz = Q(1);
  return QuadAdd(disp, QuadScale(box.ball_multiplier, constraint));
}

// Box.viewControlQuadratic i j for all i, j (as [i][j]).
std::array<std::array<Quad3, 3>, 3> ViewControlsP(const GlobalBox &box, const Pre &p) {
  std::array<Quad3, 3> corner;
  for (int i = 0; i < 3; i++) corner[i] = AdjustedViewDisplacementQuadraticP(box, p, box.triangle[i]);
  std::array<std::array<Quad3, 3>, 3> out;
  for (int i = 0; i < 3; i++) {
    out[i][i] = corner[i];
    for (int j = i + 1; j < 3; j++) {
      const Quad3 mid =
          AdjustedViewDisplacementQuadraticP(box, p, Midpoint(box.triangle[i], box.triangle[j]));
      out[i][j] = QuadSub(QuadScale(Q(2), mid), QuadScale(Q(1, 2), QuadAdd(corner[i], corner[j])));
      out[j][i] = out[i][j];
    }
  }
  return out;
}

Q BernsteinDisplacementLowerP(const GlobalBox &box, const Pre &p) {
  const auto vars = RelativeBalls(box.interval);
  const auto controls = ViewControlsP(box, p);
  Q best;
  bool first = true;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      const Q l = BernsteinLower(vars, controls[i][j]);
      if (first || l < best) best = l;
      first = false;
    }
  }
  return best;
}

// Box.viewCoefficientQuadratic and Box.coefficientBall for coefficient
// selector `which` (0 = c0, ..., 9 = czz).
RatBall CoefficientBallP(const GlobalBox &box, const Pre &p, int which) {
  auto select = [which](const Quad3 &q) -> const Q & {
    switch (which) {
    case 0: return q.c0;
    case 1: return q.cx;
    case 2: return q.cy;
    case 3: return q.cz;
    case 4: return q.cxx;
    case 5: return q.cxy;
    case 6: return q.cxz;
    case 7: return q.cyy;
    case 8: return q.cyz;
    default: return q.czz;
    }
  };
  Quad3 sum;
  for (int i = 0; i < 3; i++) {
    VecQ coeff;
    for (int c = 0; c < 3; c++) coeff[c] = select(p.contact[i][c]);
    sum = QuadAdd(sum, MulLinear(p.wcoef[i], coeff));
  }
  return QuadEvalBall(TriangleBalls(box.triangle), sum);
}

RatBall AdjustedDisplacementBallP(const GlobalBox &box, const Pre &p) {
  const Q &lambda = box.ball_multiplier;
  const RatBall b0 = BallAdd(CoefficientBallP(box, p, 0), BallConst(Q(-3) * lambda));
  const RatBall bx = CoefficientBallP(box, p, 1);
  const RatBall by = CoefficientBallP(box, p, 2);
  const RatBall bz = CoefficientBallP(box, p, 3);
  const RatBall bxx = BallAdd(CoefficientBallP(box, p, 4), BallConst(lambda));
  const RatBall bxy = CoefficientBallP(box, p, 5);
  const RatBall bxz = CoefficientBallP(box, p, 6);
  const RatBall byy = BallAdd(CoefficientBallP(box, p, 7), BallConst(lambda));
  const RatBall byz = CoefficientBallP(box, p, 8);
  const RatBall bzz = BallAdd(CoefficientBallP(box, p, 9), BallConst(lambda));
  const auto rel = RelativeBalls(box.interval);
  const RatBall &x = rel[0], &y = rel[1], &z = rel[2];
  RatBall acc = BallAdd(b0, BallMul(bx, x));
  acc = BallAdd(acc, BallMul(by, y));
  acc = BallAdd(acc, BallMul(bz, z));
  acc = BallAdd(acc, BallMul(bxx, BallMul(x, x)));
  acc = BallAdd(acc, BallMul(bxy, BallMul(x, y)));
  acc = BallAdd(acc, BallMul(bxz, BallMul(x, z)));
  acc = BallAdd(acc, BallMul(byy, BallMul(y, y)));
  acc = BallAdd(acc, BallMul(byz, BallMul(y, z)));
  acc = BallAdd(acc, BallMul(bzz, BallMul(z, z)));
  return acc;
}

Q CertifiedDisplacementLowerP(const GlobalBox &box, const Pre &p) {
  const RatBall b = AdjustedDisplacementBallP(box, p);
  return BigRat::Max(b.center - b.radius, BernsteinDisplacementLowerP(box, p));
}

bool AdmissibleP(const GlobalBox &box, const Pre &p) {
  // SignedTriangleValid root: signed coordinates nonnegative, summing to 1.
  CHECK(box.root >= 0 && box.root < 8);
  for (int i = 0; i < 3; i++) {
    Q sum(0);
    for (int c = 0; c < 3; c++) {
      const Q v = (box.root >> (2 - c)) & 1 ? -box.triangle[i][c] : box.triangle[i][c];
      if (v < Q(0)) return false;
      sum = sum + v;
    }
    if (!(sum == Q(1))) return false;
  }
  bool any_pos = false;
  for (int i = 0; i < 3; i++) {
    const Q wl = WeightLowerP(p, i);
    if (wl < Q(0)) return false;
    if (wl > Q(0)) any_pos = true;
  }
  if (!any_pos) return false;
  for (int i = 0; i < 3; i++) {
    if (!(SupportUpperP(box, p, i, box.certificate.nonzero_witness[i]) < Q(0))) return false;
  }
  return !(box.ball_multiplier < Q(0));
}

}  // namespace

Q SupportAt(const GlobalBox &box, int corner, int i, int k) {
  return Precompute(box).support_at[corner][i][k];
}
Q SupportUpper(const GlobalBox &box, int i, int k) { return SupportUpperP(box, Precompute(box), i, k); }
std::array<std::vector<Q>, 3> SupportUppers(const GlobalBox &box) {
  const Pre p = Precompute(box);
  std::array<std::vector<Q>, 3> out;
  for (int i = 0; i < 3; i++) {
    out[i].reserve(NUM_VERTICES);
    for (int k = 0; k < NUM_VERTICES; k++) out[i].push_back(SupportUpperP(box, p, i, k));
  }
  return out;
}
Q WeightAt(const GlobalBox &box, int corner, int i) { return Precompute(box).weight_at[corner][i]; }
Q WeightLower(const GlobalBox &box, int i) { return WeightLowerP(Precompute(box), i); }
Q WeightUpper(const GlobalBox &box, int i) { return WeightUpperP(Precompute(box), i); }
Q WeightedDefectUpper(const GlobalBox &box) { return WeightedDefectUpperP(box, Precompute(box)); }
Quad3 ContactQuadratic(const GlobalBox &box, int i, int c) { return Precompute(box).contact[i][c]; }
Quad3 ViewControlQuadratic(const GlobalBox &box, int i, int j) {
  return ViewControlsP(box, Precompute(box))[i][j];
}
Q BernsteinDisplacementLower(const GlobalBox &box) {
  return BernsteinDisplacementLowerP(box, Precompute(box));
}
RatBall AdjustedDisplacementBall(const GlobalBox &box) {
  return AdjustedDisplacementBallP(box, Precompute(box));
}
Q CertifiedDisplacementLower(const GlobalBox &box) {
  return CertifiedDisplacementLowerP(box, Precompute(box));
}

Q DBound(const GlobalBox &box) {
  const auto &iv = box.interval;
  const Q ex = EndpointAbsBound(iv.min[2], iv.max[2]);
  const Q ey = EndpointAbsBound(iv.min[3], iv.max[3]);
  const Q ez = EndpointAbsBound(iv.min[4], iv.max[4]);
  return Q(1) + ex * ex + ey * ey + ez * ez;
}

Q DisplacementError(const GlobalBox &box) {
  return Q(300) * DBound(box) * TightVertexErrorQ();
}

bool Admissible(const GlobalBox &box) { return AdmissibleP(box, Precompute(box)); }

Q DisplacementSlack(const GlobalBox &box) {
  const Pre p = Precompute(box);
  return CertifiedDisplacementLowerP(box, p) - DBound(box) * WeightedDefectUpperP(box, p) -
         DisplacementError(box);
}

bool Valid(const GlobalBox &box) {
  const Pre p = Precompute(box);
  if (!AdmissibleP(box, p)) return false;
  return !(CertifiedDisplacementLowerP(box, p) - DBound(box) * WeightedDefectUpperP(box, p) -
               DisplacementError(box) <
           Q(0));
}

GlobalBox ComponentBox(const MixedBox &box, int k) {
  GlobalBox g;
  g.interval = box.interval;
  g.root = box.root;
  g.triangle = box.triangle;
  g.chart = box.chart;
  g.certificate = box.component[k].certificate;
  g.inner_index = box.component[k].inner_index;
  g.ball_multiplier = box.component[k].ball_multiplier;
  return g;
}

namespace {
struct MixedPre {
  std::array<GlobalBox, 4> comps;
  std::array<Pre, 4> pre;
};
MixedPre PrecomputeMixed(const MixedBox &box) {
  MixedPre m;
  for (int k = 0; k < 4; k++) {
    m.comps[k] = ComponentBox(box, k);
    m.pre[k] = Precompute(m.comps[k]);
  }
  return m;
}
Q MixedBernsteinLowerP(const MixedBox &box, const MixedPre &m) {
  const auto vars = RelativeBalls(box.interval);
  std::array<std::array<std::array<Quad3, 3>, 3>, 4> controls;
  for (int k = 0; k < 4; k++) controls[k] = ViewControlsP(m.comps[k], m.pre[k]);
  Q best;
  bool first = true;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      Quad3 control;
      for (int k = 0; k < 4; k++) control = QuadAdd(control, QuadScale(box.weight[k], controls[k][i][j]));
      const Q l = BernsteinLower(vars, control);
      if (first || l < best) best = l;
      first = false;
    }
  }
  return best;
}
Q MixedWeightedDefectUpperP(const MixedBox &box, const MixedPre &m) {
  Q total(0);
  for (int k = 0; k < 4; k++) total = total + box.weight[k] * WeightedDefectUpperP(m.comps[k], m.pre[k]);
  return total;
}
}  // namespace

Q BernsteinDisplacementLower(const MixedBox &box) {
  return MixedBernsteinLowerP(box, PrecomputeMixed(box));
}

Q WeightedDefectUpper(const MixedBox &box) {
  return MixedWeightedDefectUpperP(box, PrecomputeMixed(box));
}

Q DisplacementSlack(const MixedBox &box) {
  const MixedPre m = PrecomputeMixed(box);
  const GlobalBox &c0 = m.comps[0];
  return MixedBernsteinLowerP(box, m) - DBound(c0) * MixedWeightedDefectUpperP(box, m) -
         DisplacementError(c0);
}

bool Valid(const MixedBox &box) {
  Q sum(0);
  for (int k = 0; k < 4; k++) {
    if (box.weight[k] < Q(0)) return false;
    sum = sum + box.weight[k];
  }
  if (!(sum == Q(1))) return false;
  const MixedPre m = PrecomputeMixed(box);
  for (int k = 0; k < 4; k++) {
    if (!AdmissibleP(m.comps[k], m.pre[k])) return false;
  }
  const GlobalBox &c0 = m.comps[0];
  return !(MixedBernsteinLowerP(box, m) - DBound(c0) * MixedWeightedDefectUpperP(box, m) -
               DisplacementError(c0) <
           Q(0));
}

// RatQuadratic3.evalTightBall in closed form: centered linear terms are
// (0, |g| r), centered cross products (0, r_i r_j), and the centered squares
// (r²/2, r²/2), all combined by exact ball addition and scaling.
RatBall QuadEvalTightBall(const std::array<RatBall, 3> &vars, const Quad3 &q) {
  const Q &x = vars[0].center, &y = vars[1].center, &z = vars[2].center;
  const Q &rx = vars[0].radius, &ry = vars[1].radius, &rz = vars[2].radius;
  const Q two(2);
  const Q gx = q.cx + two * q.cxx * x + q.cxy * y + q.cxz * z;
  const Q gy = q.cy + q.cxy * x + two * q.cyy * y + q.cyz * z;
  const Q gz = q.cz + q.cxz * x + q.cyz * y + two * q.czz * z;
  auto A = [](const Q &v) { return BigRat::Abs(v); };
  const Q sx = rx * rx / two, sy = ry * ry / two, sz = rz * rz / two;
  const Q center = QuadEvalQ(q, x, y, z) + q.cxx * sx + q.cyy * sy + q.czz * sz;
  const Q radius = A(gx) * rx + A(gy) * ry + A(gz) * rz +
                   A(q.cxx) * sx + A(q.cyy) * sy + A(q.czz) * sz +
                   A(q.cxy) * (rx * ry) + A(q.cxz) * (rx * rz) + A(q.cyz) * (ry * rz);
  return {center, radius};
}

Q SqrtQUp16(const Q &x) {
  if (!(x > Q(0))) return Q(0);
  const BigInt scale16 = BigInt::Pow(BigInt(10), 16);
  const BigInt scale32 = BigInt::Pow(BigInt(10), 32);
  const BigInt c = BigRat::Ceil(x * Q(scale32, BigInt(1)));
  return Q(BigInt::Sqrt(c) + BigInt(1), scale16);
}

bool OutsideCayleyBall(const Interval5 &iv) {
  auto min_abs = [](const Q &lo, const Q &hi) {
    if (!(lo > Q(0)) && !(hi < Q(0))) return Q(0);
    return BigRat::Min(BigRat::Abs(lo), BigRat::Abs(hi));
  };
  const Q mx = min_abs(iv.min[2], iv.max[2]);
  const Q my = min_abs(iv.min[3], iv.max[3]);
  const Q mz = min_abs(iv.min[4], iv.max[4]);
  return mx * mx + my * my + mz * mz > Q(3);
}

namespace {
// AtlasFundamentalPrune.advantageQuadratic
Quad3 AdvantageQuadratic(int chart, int direction) {
  auto num = [chart](int i, int j) { return QuadScale(ChartSign(chart, i), NumeratorQuadratic(i, j)); };
  const Quad3 a = QuadAdd(num(0, 0), num(1, 1));
  const Quad3 b = QuadSub(num(0, 1), num(1, 0));
  return QuadAdd(QuadScale(Q(-690983, 1000000), a),
                 QuadScale(Q(direction * 951057, 1000000), b));
}
}  // namespace

Q FundamentalLower(const Interval5 &iv, int chart, int direction) {
  CHECK(direction == 1 || direction == -1);
  const auto vars = RelativeBalls(iv);
  const Quad3 q = AdvantageQuadratic(chart, direction);
  const RatBall tight = QuadEvalTightBall(vars, q);
  return BigRat::Max(tight.center - tight.radius, BernsteinLower(vars, q));
}

bool FundamentalPruneValid(const Interval5 &iv, int chart, int direction) {
  return Q(2, 125000) < FundamentalLower(iv, chart, direction);
}

namespace {
// Icosahedral prune: the trace advantage of right-composing with neighbor n,
// trace(R G) - trace(R), times the Cayley denominator:
// sum_ij s_i Num_ij(w) (G~_ji - delta_ij), with G~ the rounded neighbor.
Quad3 IcoAdvantageQuadratic(int chart, int n) {
  const MatrixTable &T = solid::kSymmetryNeighbors;
  CHECK(n >= 0 && n < T.size);
  Quad3 sum;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) {
      const Q g = Q(T.num[n][3 * j + i], T.denom) - Q(i == j ? 1 : 0);
      sum = QuadAdd(sum, QuadScale(g, QuadScale(ChartSign(chart, i), NumeratorQuadratic(i, j))));
    }
  }
  return sum;
}
}  // namespace

Q IcoPruneLower(const Interval5 &iv, int chart, int n) {
  const auto vars = RelativeBalls(iv);
  const Quad3 q = IcoAdvantageQuadratic(chart, n);
  const RatBall tight = QuadEvalTightBall(vars, q);
  return BigRat::Max(tight.center - tight.radius, BernsteinLower(vars, q));
}

// Rounded tables (the snub/DH neighbors): |G - G~| < 10^-12 per entry and
// |Num_ij| <= 1 + |w|^2 <= 4 on the bounded region, so the rounding changes
// the quadratic by less than 36 * 10^-12. Exact tables (the Septopert's C3): 0.
Q IcoPruneAllowance() {
  const MatrixTable &T = solid::kSymmetryNeighbors;
  return T.exact ? Q(0) : Q(36, T.denom);
}

bool IcoPruneValid(const Interval5 &iv, int chart, int n) {
  return IcoPruneAllowance() < IcoPruneLower(iv, chart, n);
}

namespace {
Quad3 HalfTurnCoefficientQuadratic(const TriangleQ &tri, int chart, int g, int c, int d) {
  const MatrixTable &T = solid::kHalfTurnGroup;
  CHECK(g >= 0 && g < T.size && c >= 0 && c < 3 && d >= 0 && d < 3);
  auto G = [&](int i, int j) { return Q(T.num[g][3 * i + j], T.denom); };
  const VecQ &pc = tri[c], &pd = tri[d];
  VecQ gpc, gpd;
  for (int k = 0; k < 3; k++) {
    gpc[k] = G(k, 0) * pc[0] + G(k, 1) * pc[1] + G(k, 2) * pc[2];
    gpd[k] = G(k, 0) * pd[0] + G(k, 1) * pd[1] + G(k, 2) * pd[2];
  }
  const Q dot = pc[0] * pd[0] + pc[1] * pd[1] + pc[2] * pd[2];
  Quad3 sum;
  for (int i = 0; i < 3; i++) {
    for (int k = 0; k < 3; k++) {
      const Q coeff = pc[i] * gpd[k] + pd[i] * gpc[k] - dot * (G(k, i) + Q(i == k ? 1 : 0));
      sum = QuadAdd(sum, QuadScale(coeff, QuadScale(ChartSign(chart, i), NumeratorQuadratic(i, k))));
    }
  }
  return sum;
}
}  // namespace

Q HalfTurnPruneLower(const Interval5 &iv, const TriangleQ &tri, int chart, int g, int c, int d) {
  const auto vars = RelativeBalls(iv);
  const Quad3 q = HalfTurnCoefficientQuadratic(tri, chart, g, c, d);
  const RatBall tight = QuadEvalTightBall(vars, q);
  return BigRat::Max(tight.center - tight.radius, BernsteinLower(vars, q));
}

// For a table rounded to 10^-12 (the DH's icosahedral group, its tie
// half-turns): |G - G~| <= 5 * 10^-13 per entry, so
// |(G - G~) P|_k <= 5 * 10^-13 |P|_1, and |N_ik| <= 1 + |w|^2 <= 4 on the
// bounded region; summing over i, k, b_cd changes by at most
// 4 * 5 * 10^-13 * (6 |P_c|_1 |P_d|_1 + 9 |P_c . P_d|)
// (Lean: AtlasHalfTurnPrune.allowance).
static Q RoundedTableAllowance(const TriangleQ &tri, int c, int d) {
  auto l1 = [](const VecQ &p) { return BigRat::Abs(p[0]) + BigRat::Abs(p[1]) + BigRat::Abs(p[2]); };
  const Q dot = tri[c][0] * tri[d][0] + tri[c][1] * tri[d][1] + tri[c][2] * tri[d][2];
  return Q(2, 1000000000000) * (Q(6) * l1(tri[c]) * l1(tri[d]) + Q(9) * BigRat::Abs(dot));
}

// An exact table (the Septopert's Q_g, mirror_q.h) needs no allowance.
Q HalfTurnPruneAllowance(const TriangleQ &tri, int c, int d) {
  return solid::kHalfTurnGroup.exact ? Q(0) : RoundedTableAllowance(tri, c, d);
}

bool HalfTurnPruneValid(const Interval5 &iv, const TriangleQ &tri, int chart, int g) {
  for (int c = 0; c < 3; c++) {
    for (int d = c; d < 3; d++) {
      if (!(HalfTurnPruneAllowance(tri, c, d) < HalfTurnPruneLower(iv, tri, chart, g, c, d))) return false;
    }
  }
  return true;
}

namespace {
Quad3 TieCoefficientQuadratic(const TriangleQ &tri, int chart, int n, const Q &tau, int c, int d) {
  const MatrixTable &T = solid::kTieHalfTurns;
  CHECK(n >= 0 && n < T.size && c >= 0 && c < 3 && d >= 0 && d < 3);
  auto G = [&](int i, int j) { return Q(T.num[n][3 * i + j], T.denom); };
  const VecQ &pc = tri[c], &pd = tri[d];
  VecQ gpc, gpd;
  for (int k = 0; k < 3; k++) {
    gpc[k] = G(k, 0) * pc[0] + G(k, 1) * pc[1] + G(k, 2) * pc[2];
    gpd[k] = G(k, 0) * pd[0] + G(k, 1) * pd[1] + G(k, 2) * pd[2];
  }
  const Q dot = pc[0] * pd[0] + pc[1] * pd[1] + pc[2] * pd[2];
  Quad3 sum;
  for (int i = 0; i < 3; i++) {
    for (int k = 0; k < 3; k++) {
      const Q coeff = pc[i] * gpd[k] + pd[i] * gpc[k] - dot * G(k, i);
      sum = QuadAdd(sum, QuadScale(coeff, QuadScale(ChartSign(chart, i), NumeratorQuadratic(i, k))));
    }
  }
  return QuadSub(sum, QuadScale(tau * dot, DenomQuadratic()));
}
}  // namespace

Q TieLeafLower(const Interval5 &iv, const TriangleQ &tri, int chart, int n, const Q &rho, int c, int d) {
  const Q tau = (Q(3) - rho * rho) / (Q(1) + rho * rho);
  const auto vars = RelativeBalls(iv);
  const Quad3 q = TieCoefficientQuadratic(tri, chart, n, tau, c, d);
  const RatBall tight = QuadEvalTightBall(vars, q);
  return BigRat::Max(tight.center - tight.radius, BernsteinLower(vars, q));
}

Q KLower(const KQ &x) {
  // IcoField.sqrt5Lo/Hi, s72Lo/Hi; IcoQ.lo.
  static const Q s5lo(std::string_view("22360679774997896964091736/10000000000000000000000000"));
  static const Q s5hi(std::string_view("22360679774997896964091737/10000000000000000000000000"));
  static const Q slo(std::string_view("9510565162951535721164393/10000000000000000000000000"));
  static const Q shi(std::string_view("9510565162951535721164394/10000000000000000000000000"));
  auto lomul = [](const Q &k, const Q &l, const Q &u) { return Q::Sign(k) >= 0 ? k * l : k * u; };
  return x.a + lomul(x.b, s5lo, s5hi) + lomul(x.c, slo, shi) + lomul(x.d, s5lo * slo, s5hi * shi);
}

bool CapLeafValid(const Interval5 &iv, const TriangleQ &tri, int chart, const CapExact &cap) {
  if (chart != 0) return false;
  Q w2(0);
  for (int a = 2; a < 5; a++) {
    const Q lo2 = iv.min[a] * iv.min[a], hi2 = iv.max[a] * iv.max[a];
    w2 = w2 + (lo2 < hi2 ? hi2 : lo2);
  }
  if (cap.wmax2 < w2) return false;
  auto dot = [&](const VecQ &p, int f) {
    KQ r{Q(0), Q(0), Q(0), Q(0)};
    for (int a = 0; a < 3; a++) {
      const KQ &c = cap.frame[f][a];
      r = {r.a + p[a] * c.a, r.b + p[a] * c.b, r.c + p[a] * c.c, r.d + p[a] * c.d};
    }
    return r;
  };
  auto comb = [](const Q &m, const KQ &x, const Q &s, const KQ &y) {
    return KQ{m * x.a + s * y.a, m * x.b + s * y.b, m * x.c + s * y.c, m * x.d + s * y.d};
  };
  for (const VecQ &p : tri) {
    const KQ px = dot(p, 0);
    if (!(Q(0) < KLower(px))) return false;
    for (int f = 1; f <= 2; f++) {
      const KQ pf = dot(p, f);
      if (KLower(comb(cap.mu0, px, Q(-1), pf)) < Q(0)) return false;
      if (KLower(comb(cap.mu0, px, Q(1), pf)) < Q(0)) return false;
    }
  }
  return true;
}

TQ TAdd(const TQ &x, const TQ &y) { return {x.a + y.a, x.b + y.b, x.c + y.c}; }
TQ TSub(const TQ &x, const TQ &y) { return {x.a - y.a, x.b - y.b, x.c - y.c}; }
TQ TScale(const Q &k, const TQ &x) { return {k * x.a, k * x.b, k * x.c}; }
TQ TMul(const TQ &x, const TQ &y) {
  // TribQ.mul: t^3 = t^2 + t + 1, t^4 = 2 t^2 + 2 t + 1.
  const Q p3 = x.b * y.c + x.c * y.b, p4 = x.c * y.c;
  return {x.a * y.a + p3 + p4, x.a * y.b + x.b * y.a + p3 + Q(2) * p4,
          x.a * y.c + x.b * y.b + x.c * y.a + p3 + Q(2) * p4};
}
namespace {
const Q &TribLo() {
  static const Q q(std::string_view("18392867552141611325518525646532/10000000000000000000000000000000"));
  return q;
}
const Q &TribHi() {
  static const Q q(std::string_view("18392867552141611325518525646533/10000000000000000000000000000000"));
  return q;
}
}  // namespace
Q TLower(const TQ &x) {
  // TribQ.lo.
  auto lomul = [](const Q &k, const Q &l, const Q &u) { return Q::Sign(k) >= 0 ? k * l : k * u; };
  return x.a + lomul(x.b, TribLo(), TribHi()) + lomul(x.c, TribLo() * TribLo(), TribHi() * TribHi());
}
Q TUpper(const TQ &x) {
  // TribQ.hi.
  auto himul = [](const Q &k, const Q &l, const Q &u) { return Q::Sign(k) >= 0 ? k * u : k * l; };
  return x.a + himul(x.b, TribLo(), TribHi()) + himul(x.c, TribLo() * TribLo(), TribHi() * TribHi());
}
double TDouble(const TQ &x) {
  const double t = 1.839286755214161132551852564653286600424178746097592246778758639404203222081966425738435419428307014141979826859240974164178450746507436943831545820499513796249655539644613666121540277972678118941041;
  return x.a.ToDouble() + x.b.ToDouble() * t + x.c.ToDouble() * t * t;
}

namespace {
TQ TDot(const VecQ &p, const std::array<TQ, 3> &v) {
  TQ r{Q(0), Q(0), Q(0)};
  for (int a = 0; a < 3; a++) r = TAdd(r, TScale(p[a], v[a]));
  return r;
}
TQ TDotT(const std::array<TQ, 3> &u, const std::array<TQ, 3> &v) {
  TQ r{Q(0), Q(0), Q(0)};
  for (int a = 0; a < 3; a++) r = TAdd(r, TMul(u[a], v[a]));
  return r;
}
// Lower bound of k w over w in [lo, hi] for k in [kl, kh] (TribQ enclosure).
Q MulIvlLower(const Q &kl, const Q &kh, const Q &lo, const Q &hi) {
  Q m = kl * lo;
  for (const Q &c : {kl * hi, kh * lo, kh * hi}) if (c < m) m = c;
  return m;
}
}  // namespace

// Lean: KCapClaim.tribCapLeafOk (the same constraints, in the same order).
bool TribCapLeafValid(const Interval5 &iv, const TriangleQ &tri, int chart, const TribCap &cap) {
  if (chart != 0) return false;
  const auto &x = cap.frame[0], &e1 = cap.frame[1], &e2 = cap.frame[2];
  const TQ xx = TDotT(x, x), n1 = TDotT(e1, e1), n2 = TDotT(e2, e2);
  // f = alpha + sum_i w_i beta_i at a corner: its lower bound over the box.
  auto lower = [&](const TQ &alpha, const std::array<TQ, 3> &beta) {
    Q l = TLower(alpha);
    for (int i = 0; i < 3; i++)
      l = l + MulIvlLower(TLower(beta[i]), TUpper(beta[i]), iv.min[2 + i], iv.max[2 + i]);
    return l;
  };
  const std::array<TQ, 3> zero3{TQ{Q(0), Q(0), Q(0)}, TQ{Q(0), Q(0), Q(0)}, TQ{Q(0), Q(0), Q(0)}};
  auto scaled = [](const TQ &k, const std::array<TQ, 3> &v) {
    return std::array<TQ, 3>{TMul(k, v[0]), TMul(k, v[1]), TMul(k, v[2])};
  };
  auto neg = [](const std::array<TQ, 3> &v) {
    std::array<TQ, 3> r;
    for (int i = 0; i < 3; i++) r[i] = TScale(Q(-1), v[i]);
    return r;
  };
  for (const VecQ &P : tri) {
    // A = P.x / |x|^2, C_i = P.e_i / |e_i|^2, all times |x|^2 |e1|^2 |e2|^2 > 0:
    // a' = (P.x) |e1|^2 |e2|^2, c1' = (P.e1) |x|^2 |e2|^2, c2' = (P.e2) |x|^2 |e1|^2.
    const TQ px = TDot(P, x), p1 = TDot(P, e1), p2 = TDot(P, e2);
    const TQ A = TMul(px, TMul(n1, n2)), C1 = TMul(p1, TMul(xx, n2)), C2 = TMul(p2, TMul(xx, n1));
    if (!(Q(0) < TLower(A))) return false;
    if (cap.kind == 0) {
      // |c_i| <= mu0 a.
      for (const TQ &C : {C1, C2}) {
        if (Q::Sign(lower(TSub(TScale(cap.mu0, A), C), zero3)) < 0) return false;
        if (Q::Sign(lower(TAdd(TScale(cap.mu0, A), C), zero3)) < 0) return false;
      }
    } else {
      const TQ M = TScale(Q(-1), C1);
      // 0 <= m <= mu0 a; |c2| <= t0 m.
      if (Q::Sign(lower(M, zero3)) < 0) return false;
      if (Q::Sign(lower(TSub(TScale(cap.mu0, A), M), zero3)) < 0) return false;
      if (Q::Sign(lower(TSub(TScale(cap.t0, M), C2), zero3)) < 0) return false;
      if (Q::Sign(lower(TAdd(TScale(cap.t0, M), C2), zero3)) < 0) return false;
      // |(w.F / |F|^2) a - s_F m| <= t0 m, times |F|^2: |(w.F) a - s_F |F|^2 m| <= t0 |F|^2 m.
      for (int f = 0; f < 3; f++) {
        const auto &F = cap.frame[3 + f];
        const TQ FF = TDotT(F, F);
        const Q sF = f == 0 ? cap.s0 : Q(0);
        const TQ base = TMul(FF, M);
        const std::array<TQ, 3> beta = scaled(A, F);
        // t0 |F|^2 m - (w.F) a + s_F |F|^2 m >= 0 and t0 |F|^2 m + (w.F) a - s_F |F|^2 m >= 0.
        if (Q::Sign(lower(TAdd(TScale(cap.t0, base), TScale(sF, base)), neg(beta))) < 0) return false;
        if (Q::Sign(lower(TSub(TScale(cap.t0, base), TScale(sF, base)), beta)) < 0) return false;
      }
    }
  }
  if (cap.kind == 0) {
    // |w.F| <= R mu0 |F|^2 on the box.
    for (int f = 0; f < 3; f++) {
      const auto &F = cap.frame[3 + f];
      const TQ bound = TScale(cap.R * cap.mu0, TDotT(F, F));
      if (Q::Sign(lower(bound, neg(F))) < 0) return false;
      if (Q::Sign(lower(bound, F)) < 0) return false;
    }
  }
  return true;
}

bool TieLeafValid(const Interval5 &iv, const TriangleQ &tri, int chart, int n, const Q &rho) {
  for (int c = 0; c < 3; c++) {
    for (int d = c; d < 3; d++) {
      if (!(RoundedTableAllowance(tri, c, d) < TieLeafLower(iv, tri, chart, n, rho, c, d))) return false;
    }
  }
  return true;
}

Q IdentityMismatchRadius(const Interval5 &iv) {
  Q sum(0);
  for (int a = 2; a < 5; a++) {
    const RatBall b = BallOfEndpoints(iv.min[a], iv.max[a]);
    const Q upper = BigRat::Abs(b.center) + b.radius;
    sum = sum + upper * upper;
  }
  return Q(2) * SqrtQUp16(sum);
}

bool IdentityTubeValid(const Interval5 &iv, const Q &r) {
  return !(r < IdentityMismatchRadius(iv));
}

Interval5 RestrictedRootInterval(int chart) {
  CHECK(chart >= 0 && chart <= 3);
  // The root interval (AtlasPose.rootInterval): the Cayley cube [-1, 1]^3.
  Interval5 iv;
  iv.min = {Q(0), Q(0), Q(-1), Q(-1), Q(-1)};
  iv.max = {Q(8, 5), Q(4), Q(1), Q(1), Q(1)};
  // With the fivefold symmetry (AtlasFundamentalPrune.restrictedRootInterval),
  // charts 0-2 narrow one coordinate to [-1/3, 1/3]. (The Septopert, C3v:
  // every chart is searched over the whole cube.)
  if (solid::kFivefold) {
    static constexpr int kCoordinate[4] = {4, 3, 2, 4};
    const Q width = chart == 3 ? Q(1) : Q(1, 3);
    iv.min[kCoordinate[chart]] = -width;
    iv.max[kCoordinate[chart]] = width;
  }
  return iv;
}

}  // namespace exact5d
