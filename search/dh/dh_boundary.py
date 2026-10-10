#!/usr/bin/env python3
"""The deltoidal hexecontahedron is a limit of Rupert polyhedra.

Scaling the DH's twelve 5-fold vertices by (1 + eta) (keeping the full
icosahedral symmetry; the kites fold slightly) gives a Rupert polyhedron for
small eta > 0. This script checks one passage in 50-digit arithmetic: for
eta = 1/1000 and the pose below (found by a sequential-LP maximizer near an
exact tie of the DH), every vertex of the rotated copy projects strictly
inside the projected hull of the original (translation 0 suffices: both
shadows are centrally symmetric).

The pose is near a "pinning tie" of the exact DH: for the plane x^perp through
an antipodal pair of 5-fold vertices and an antipodal pair of 2-fold vertices,
and views u in a wedge around x, the rotation sigma_u sigma_x (a product of
reflections) maps the DH to a copy whose shadow along u lies inside the DH's
shadow and touches it (clearance exactly 0). Pushing the 5-fold vertices out
turns these ties into passages of clearance ~0.07 eta.

Usage: python3 dh_boundary.py [model=dh_model.txt] [eta=1/1000]
"""

import sys
from decimal import Decimal as D, getcontext
from fractions import Fraction as F

getcontext().prec = 50
model = sys.argv[1] if len(sys.argv) > 1 else "dh_model.txt"
eta = F(sys.argv[2]) if len(sys.argv) > 2 else F(1, 1000)

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


r5 = max(norm(v) for v in V)
scale = 1 + D(eta.numerator) / D(eta.denominator)
K = [[c * scale for c in v] if norm(v) > r5 - D(10) ** -9 else v for v in V]
assert sum(1 for v in V if norm(v) > r5 - D(10) ** -9) == 12

# The pose (model frame of dh_model.py): outer view u, inner = rotation by
# theta about axis.
u = [D("0.550514665573163"), D("0.240411776415775"), D("0.799459680502700")]
axis = [D("0.780519048871"), D("-0.489211602134"), D("-0.389181220882")]
theta = D("0.29777989521899473")
u = [c / norm(u) for c in u]
axis = [c / norm(axis) for c in axis]


def cos_sin(t):
    c, s, term = D(0), D(0), D(1)
    for k in range(80):
        if k % 4 == 0: c += term
        elif k % 4 == 1: s += term
        elif k % 4 == 2: c -= term
        else: s -= term
        term = term * t / (k + 1)
    return c, s


c, s = cos_sin(theta)


def rot(v):
    d, ax = dot(axis, v), cross(axis, v)
    return [v[i] * c + ax[i] * s + axis[i] * d * (1 - c) for i in range(3)]


e1 = cross(u, [D(0), D(0), D(1)])
e1 = [x / norm(e1) for x in e1]
e2 = cross(u, e1)
outer = [(dot(v, e1), dot(v, e2)) for v in K]
inner = [(dot(rot(v), e1), dot(rot(v), e2)) for v in K]


def cr(o, p, q): return (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0])


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


m = min(depth(q) for q in inner)
print(f"eta = {eta}: min depth of the rotated copy's vertices inside the shadow = {m:.6e}")
print("RUPERT (strict passage)" if m > 0 else "no passage at this pose")
