#!/usr/bin/env python3
"""The exact deltoidal hexecontahedron in the model frame, over the field
K = Q(sqrt5, s), s = sin 72 degrees (s^2 = (5 + sqrt5)/8).

dh_model.py rotates McCooey's coordinates (in Q(sqrt5)) into the snub's frame
(z a 5-fold vertex direction, x a 2-fold one) and scales them to norm < 1.
The frame vectors are in K^3 (|2-fold vertex| = sqrt5, |5-fold vertex| =
sqrt(100 + 40 sqrt5)/6 = (sqrt5/3) tan 72 deg), so every vertex of the
unscaled solid has coordinates in K. This script computes them exactly (each
coordinate as four rationals a + b sqrt5 + c s + d s sqrt5) and checks them
against dh_model.txt up to the common scale.

Writes dh_exact.txt: "kvertex <slot> a b c d  a b c d  a b c d" (x, y, z) for
the 70 slots, and "pinning a b c d ..." for the pinning plane normal
x = (cos 18, sin 18, 2) (unnormalized; cos 18 = s, sin 18 = (sqrt5 - 1)/4).

Usage: python3 dh_exact.py [model=dh_model.txt] [out=dh_exact.txt]
"""

import itertools
import math
import sys
from fractions import Fraction as F

model = sys.argv[1] if len(sys.argv) > 1 else "dh_model.txt"
out = sys.argv[2] if len(sys.argv) > 2 else "dh_exact.txt"
R5 = math.sqrt(5)
S72 = math.sqrt((5 + R5) / 8)


class K:
    __slots__ = ("v",)

    def __init__(self, a=0, b=0, c=0, d=0):
        self.v = (F(a), F(b), F(c), F(d))

    def __add__(x, y): return K(*(p + q for p, q in zip(x.v, y.v)))
    def __neg__(x): return K(*(-p for p in x.v))
    def __sub__(x, y): return x + (-y)

    def __mul__(x, y):
        if not isinstance(y, K): y = K(y)
        a, b, c, d = x.v
        e, f, g, h = y.v
        p, q = c * g + 5 * d * h, c * h + d * g
        return K(a * e + 5 * b * f + (5 * p + 5 * q) / 8, a * f + b * e + (p + 5 * q) / 8,
                 a * g + 5 * b * h + c * e + 5 * d * f, a * h + b * g + c * f + d * e)
    __rmul__ = __mul__

    def __eq__(x, y): return x.v == y.v
    def f(x): return float(x.v[0]) + float(x.v[1]) * R5 + float(x.v[2]) * S72 + float(x.v[3]) * R5 * S72

    def inv(x):
        # 1/x: multiply by conjugates. x = A + B s with A, B in Q(sqrt5).
        a, b, c, d = x.v
        A, B = K(a, b), K(c, d)
        # (A + B s)(A - B s) = A^2 - B^2 s^2, in Q(sqrt5).
        s2 = K(F(5, 8), F(1, 8))
        n = A * A - B * B * s2
        na, nb = n.v[0], n.v[1]
        assert n.v[2] == 0 and n.v[3] == 0
        # 1/(na + nb sqrt5) = (na - nb sqrt5)/(na^2 - 5 nb^2)
        den = na * na - 5 * nb * nb
        ninv = K(na / den, -nb / den)
        return (A - B * K(0, 0, 1)) * ninv


SQ5 = K(0, 1)
S = K(0, 0, 1)
C72 = K(F(-1, 4), F(1, 4))
TAN72 = S * C72.inv()


def dot(a, b): return sum((p * q for p, q in zip(a, b)), K())
def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


# McCooey's coordinates (Q(sqrt5)).
C = [K(F(5, 4), F(-1, 4)), K(F(15, 22), F(1, 22)), K(0, F(1, 2)), K(F(5, 6), F(1, 6)), K(F(5, 11), F(4, 11)),
     K(F(5, 4), F(1, 4)), K(F(5, 6), F(3, 6)), K(F(25, 22), F(9, 22)), K(0, 1)]
Z = K()
verts = []
for a, b, c in [(Z, Z, C[8]), (Z, C[1], C[7]), (C[3], Z, C[6]), (C[0], C[2], C[5]), (C[4], C[4], C[4])]:
    for sa, sb, sc in itertools.product((1, -1), repeat=3):
        p = [a * sa, b * sb, c * sc]
        for q in (p, [p[2], p[0], p[1]], [p[1], p[2], p[0]]):
            if not any(q == w for w in verts):
                verts.append(q)
assert len(verts) == 62

# The model's frame (as dh_model.py): five = the first vertex of maximal norm
# (in dh_model.py's float order, which is this order), two = a 2-fold vertex
# perpendicular to it; dh_model.txt fixes which, so find the rotation that
# matches it.
lines = [l.split() for l in open(model)]
mv = {int(t[1]): [float(x) for x in t[2:5]] for t in lines if t and t[0] == "vertex"}
mnorm = max(math.sqrt(sum(c * c for c in v)) for v in mv.values())
norm2 = [dot(v, v) for v in verts]
r5sq = max(norm2, key=lambda k: k.f())
five = next(v for v, n in zip(verts, norm2) if n == r5sq)
# |five| = (sqrt5 / 3) tan 72 (check numerically and exactly).
nfive = SQ5 * TAN72 * F(1, 3)
assert nfive * nfive == r5sq, "5-fold norm not (sqrt5/3) tan 72"
e3 = [c * nfive.inv() for c in five]
best = None
for two in verts:
    if not (dot(two, two) == K(5)) or not (dot(two, five) == K()):
        continue
    e1 = [c * SQ5.inv() for c in two]
    e2 = cross(e3, e1)
    cand = [[dot(e, v) for e in (e1, e2, e3)] for v in verts]
    scale = mnorm / max(math.sqrt(sum(c.f() ** 2 for c in v)) for v in cand)
    ok = True
    slots = {}
    for slot, p in mv.items():
        hit = [i for i, v in enumerate(cand) if max(abs(c.f() * scale - x) for c, x in zip(v, p)) < 1e-12]
        if len(hit) != 1:
            ok = False
            break
        slots[slot] = hit[0]
    if ok:
        best = (cand, slots, scale)
        break
assert best is not None, "no frame matches dh_model.txt"
cand, slots, scale = best
# Exact checks: orthonormal frame, vertices of norm r5 on z.
assert dot(e3, e3) == K(1)
x = [S, K(F(-1, 4), F(1, 4)), K(2)]
pinned = [i for i, v in enumerate(cand) if dot(v, x) == K()]
assert len(pinned) == 4, pinned


def kstr(k): return " ".join(f"{q.numerator}/{q.denominator}" for q in k.v)


with open(out, "w") as f:
    f.write(f"# Exact deltoidal hexecontahedron in dh_model's frame (McCooey scale; model = {scale!r} x this)\n")
    for slot in sorted(slots):
        f.write(f"kvertex {slot} " + "  ".join(kstr(c) for c in cand[slots[slot]]) + "\n")
    f.write("pinning " + "  ".join(kstr(c) for c in x) + "\n")
print(f"wrote {out}: 70 slots in K, model scale {scale:.15f}; pinning plane x = (cos18, sin18, 2) holds "
      f"{len(pinned)} vertices exactly")
