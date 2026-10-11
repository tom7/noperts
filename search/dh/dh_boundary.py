#!/usr/bin/env python3
"""The deltoidal hexecontahedron is a limit of Rupert polyhedra.

Scaling the DH's twelve 5-fold vertices by (1 + eta) (keeping the full
icosahedral symmetry; the kites fold slightly) gives a Rupert polyhedron for
every small eta > 0, so no neighbourhood of the DH, however small, contains
only noperts. This script checks passages in 60-digit arithmetic: for each
eta, every vertex of the rotated copy projects strictly inside the projected
hull of the original (translation 0 suffices: both shadows are centrally
symmetric).

The passages are near a "pinning tie" of the exact DH: for the plane x^perp
through an antipodal pair of 5-fold vertices and an antipodal pair of 2-fold
vertices, and views u in a wedge around x, the rotation H_u H_x (a product of
half-turns, i.e. of reflections) maps the DH to a copy whose shadow along u
lies inside the DH's shadow and touches it (clearance exactly 0). The script
computes that tie pose for a fixed view u, and checks that its clearance is 0
at eta = 0. A sequential-LP maximizer found the pose P(1/1000) for
eta = 1/1000; the pose for eta is the linear interpolation P(eta) = tie pose +
(eta / (1/1000)) (P(1/1000) - tie pose), in rotation-vector coordinates. Its
clearance is 0.0695 eta to first order (measured 2026-10-10 for eta = 10^-3
down to 10^-18), so pushing the 5-fold vertices out by any amount opens a
passage. (Numerical, though with 60 digits; not part of the Lean result.)

Pushing them in (eta < 0) makes this tie's clearance negative; whether those
solids are Rupert is not known.

Usage: python3 dh_boundary.py [model=dh_model.txt] [eta ...]
  (default etas: 1/1000 1/10^4 1/10^6 1/10^9 1/10^12 1/10^18)
"""

import math
import sys
from decimal import Decimal as D, getcontext
from fractions import Fraction as F

getcontext().prec = 60
model = sys.argv[1] if len(sys.argv) > 1 else "dh_model.txt"
etas = [F(e) for e in sys.argv[2:]] or [F(1, 10**k) for k in (3, 4, 6, 9, 12, 18)]

V = []
for line in open(model):
    t = line.split()
    if t and t[0] == "vertex":
        p = [D(x) for x in t[2:5]]
        if not any(max(abs(a - b) for a, b in zip(p, q)) < D(10) ** -30 for q in V):
            V.append(p)
assert len(V) == 62, len(V)


def dot(a, b): return sum(x * y for x, y in zip(a, b))
def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
def norm(a): return dot(a, a).sqrt()
def unit(a): return [c / norm(a) for c in a]
def dec(f): return D(f.numerator) / D(f.denominator)


# The 12 5-fold vertices are the farthest; the 30 2-fold vertices are the
# middle radius (the 20 3-fold vertices are the nearest).
radius = sorted(set(round(norm(v), 9) for v in V))
assert len(radius) == 3
fold5 = [v for v in V if round(norm(v), 9) == radius[2]]
fold2 = [v for v in V if round(norm(v), 9) == radius[1]]
assert len(fold5) == 12 and len(fold2) == 30


def cos_sin(t):
    c, s, term = D(0), D(0), D(1)
    for k in range(100):
        if k % 4 == 0: c += term
        elif k % 4 == 1: s += term
        elif k % 4 == 2: c -= term
        else: s -= term
        term = term * t / (k + 1)
    return c, s


def rotate(rv, v):
    """Rotates v by the rotation vector rv (axis * angle)."""
    th = norm(rv)
    axis = [x / th for x in rv]
    c, s = cos_sin(th)
    d, ax = dot(axis, v), cross(axis, v)
    return [v[i] * c + ax[i] * s + axis[i] * d * (1 - c) for i in range(3)]


# The pose found for eta = 1/1000 (model frame of dh_model.py): outer view u,
# inner = rotation by theta about axis.
ETA0 = F(1, 1000)
u = unit([D("0.550514665573163"), D("0.240411776415775"), D("0.799459680502700")])
axis = unit([D("0.780519048871"), D("-0.489211602134"), D("-0.389181220882")])
theta = D("0.29777989521899473")
rv0 = [a * theta for a in axis]

# The pinning tie nearest to it, at the same view u: H_u H_x is the rotation
# about x cross u (or its negative) by twice the angle between u and x.
best = None
for p in fold5:
    for q in fold2:
        n = cross(p, q)
        if norm(n) < D(10) ** -20: continue
        for x in (unit(n), [-c for c in unit(n)]):
            c_target = dot(u, x)
            t = D(math.acos(float(c_target)))
            for _ in range(8):  # Newton: cos t = c_target
                c, s = cos_sin(t)
                t += (c - c_target) / s
            for sign in (1, -1):
                rv = [sign * a * 2 * t for a in unit(cross(x, u))]
                d = norm([rv[i] - rv0[i] for i in range(3)])
                if best is None or d < best[0]: best = (d, rv)
assert best[0] < D("0.01"), best[0]
rv_tie = best[1]

e1 = unit(cross(u, [D(0), D(0), D(1)]))
e2 = cross(u, e1)


def cr(o, p, q): return (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0])


def clearance(eta, rv):
    """Min depth of the rotated copy's vertices inside the shadow along u."""
    scale = 1 + dec(eta)
    K = [[c * scale for c in v] if round(norm(v), 9) == radius[2] else v for v in V]
    outer = [(dot(v, e1), dot(v, e2)) for v in K]
    inner = [(dot(w, e1), dot(w, e2)) for w in (rotate(rv, v) for v in K)]
    pts = sorted(set(outer))
    lo, up = [], []
    for p in pts:
        while len(lo) >= 2 and cr(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(up) >= 2 and cr(up[-2], up[-1], p) <= 0: up.pop()
        up.append(p)
    H = lo[:-1] + up[:-1]

    def depth(q):
        return min(cr(H[i], H[(i + 1) % len(H)], q) /
                   ((H[(i + 1) % len(H)][0] - H[i][0]) ** 2 + (H[(i + 1) % len(H)][1] - H[i][1]) ** 2).sqrt()
                   for i in range(len(H)))
    return min(depth(q) for q in inner)


print(f"tie pose, eta = 0: clearance {clearance(F(0), rv_tie):.3e} (0 up to rounding)")
for eta in etas:
    rv = [rv_tie[i] + dec(eta / ETA0) * (rv0[i] - rv_tie[i]) for i in range(3)]
    m = clearance(eta, rv)
    verdict = "RUPERT (strict passage)" if m > 0 else "no passage at this pose"
    print(f"eta = {eta}: clearance {m:.6e} = {m / dec(eta):.5f} eta: {verdict}")
