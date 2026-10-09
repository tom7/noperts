#!/usr/bin/env python3
"""The deltoidal hexecontahedron's model file (for codebdd --model_file).

The deltoidal hexecontahedron (DH) is the Catalan solid dual to the
rhombicosidodecahedron: 62 vertices (12 of degree 5 on the 5-fold axes, 20 of
degree 3 on the 3-fold axes, 30 of degree 4 on the 2-fold axes) and 60 kite
faces. Its symmetry group is the full icosahedral group Ih (with reflections).

- The exact solid: David McCooey's coordinates (as in cc-lib's
  DeltoidalHexecontahedron(), geom/polyhedra.cc), to 80 digits, rotated into
  the snub dodecahedron's frame (z a 5-fold axis, x a perpendicular 2-fold
  axis; the solid is mirror-symmetric, so every such frame gives the same
  vertex set) and scaled so that the largest vertex has norm just below 1.
- The rational model: every coordinate rounded to a multiple of 2^-64
  (`rational_vertex` lines, used verbatim by codebdd). The kites are planar
  only to ~1e-19: no rational model can make all of them planar, since each
  vertex of degree 4 lies on four kites. codebdd takes its facet planes from
  the `face` lines (--model_faces), so the codes see 60 kites.
- Vertex S k + s is seed s rotated by 2 pi k / 5 (S = 14 seeds). The two
  vertices on the z axis are listed once per C5 orbit (5 times), as for the
  pentagonal hexecontahedron.

Lines written: name, seeds, vertex i x y z (40 digits), rational_vertex i p/q
p/q p/q, face ..., and the view_triangle and neighbor lines of the snub
dodecahedron's model (the same frame and group).

Usage: python3 dh_model.py [snub=snub_model.txt] [out=dh_model.txt]
"""

import itertools
import math
import sys
from decimal import Decimal as D, getcontext
from fractions import Fraction as F

getcontext().prec = 90
TOL = D(10) ** -60
snub_file = sys.argv[1] if len(sys.argv) > 1 else "snub_model.txt"
out_file = sys.argv[2] if len(sys.argv) > 2 else "dh_model.txt"

s5 = D(5).sqrt()
C0, C1, C2 = (5 - s5) / 4, (15 + s5) / 22, s5 / 2
C3, C4, C5 = (5 + s5) / 6, (5 + 4 * s5) / 11, (5 + s5) / 4
C6, C7, C8 = (5 + 3 * s5) / 6, (25 + 9 * s5) / 22, s5


def dot(a, b): return sum(x * y for x, y in zip(a, b))
def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
def norm(a): return dot(a, a).sqrt()
def sub(a, b): return [x - y for x, y in zip(a, b)]
def close(a, b): return all(abs(x - y) < TOL for x, y in zip(a, b))


# McCooey's vertices: the cyclic permutations of these, with all signs.
verts = []
for a, b, c in [(0, 0, C8), (0, C1, C7), (C3, 0, C6), (C0, C2, C5), (C4, C4, C4)]:
    for sa, sb, sc in itertools.product((1, -1), repeat=3):
        p = [sa * D(a), sb * D(b), sc * D(c)]
        for q in (p, [p[2], p[0], p[1]], [p[1], p[2], p[0]]):
            if not any(close(q, w) for w in verts):
                verts.append(q)
assert len(verts) == 62, len(verts)

# Faces (kites) of the exact solid.
n = len(verts)
faces = []
for i, j, k in itertools.combinations(range(n), 3):
    nv = cross(sub(verts[j], verts[i]), sub(verts[k], verts[i]))
    if norm(nv) < TOL:
        continue
    d = dot(nv, verts[i])
    vals = [dot(nv, v) - d for v in verts]
    if any(x > TOL for x in vals) and any(x < -TOL for x in vals):
        continue
    face = tuple(m for m in range(n) if abs(vals[m]) < TOL)
    if face not in faces:
        faces.append(face)
assert len(faces) == 60 and all(len(f) == 4 for f in faces), (len(faces), {len(f) for f in faces})

# The frame: z along a degree-5 vertex (a 5-fold axis), x along a degree-4
# vertex perpendicular to it (a 2-fold axis), chosen so that the frame's
# icosahedral rotations are the snub model's: the 12 neighbor rotations
# (by +-72 degrees about the 5-fold axes, snub_model.txt) must preserve the
# vertex set. (Of the 10 choices of x, half give the mirror-image
# arrangement of the axes.)
lines = open(snub_file).read().splitlines()
passthrough = [l for l in lines if l.split() and l.split()[0] in ("view_triangle", "neighbor")]
neighbors = [[D(x) for x in l.split()[1:10]] for l in passthrough if l.split()[0] == "neighbor"]
assert len(neighbors) == 12
norms = sorted({round(float(norm(v)), 9) for v in verts})
r5 = max(norms)
five = next(v for v in verts if abs(float(norm(v)) - r5) < 1e-9)
e3 = [x / norm(five) for x in five]


def frame_ok(fv):
    for g in neighbors:
        for v in fv:
            w = [sum(g[3 * i + j] * v[j] for j in range(3)) for i in range(3)]
            if not any(max(abs(a - b) for a, b in zip(w, u)) < D(10) ** -35 for u in fv):
                return False
    return True


fv = None
for two in verts:
    if abs(float(norm(two)) - norms[1]) > 1e-9 or abs(dot(two, five)) > TOL:
        continue
    e1 = [x / norm(two) for x in two]
    e2 = cross(e3, e1)
    cand = [[dot(e, v) for e in (e1, e2, e3)] for v in verts]
    rmax = max(norm(v) for v in cand)
    scale = (D(1) - D(10) ** -9) / rmax
    cand = [[x * scale for x in v] for v in cand]
    if frame_ok(cand):
        fv = cand
        break
assert fv is not None, "no frame matches the snub model's group"

# C5 order: seeds have azimuth in [0, 72) degrees (axis vertices: azimuth
# 0), sorted by decreasing z; vertex S k + s is seed s rotated by 2 pi k / 5.
def az(v): return math.atan2(float(v[1]), float(v[0])) % (2 * math.pi)
def on_axis(v): return abs(float(v[0])) < 1e-30 and abs(float(v[1])) < 1e-30
seeds = [i for i, v in enumerate(fv) if on_axis(v) or az(v) < 2 * math.pi / 5 - 1e-12]
assert len(seeds) == 14, len(seeds)
seeds.sort(key=lambda i: (-float(fv[i][2]), az(fv[i])))
order = []
for k in range(5):
    c, s = math.cos(2 * math.pi * k / 5), math.sin(2 * math.pi * k / 5)
    for i in seeds:
        v = fv[i]
        target = (c * float(v[0]) - s * float(v[1]), s * float(v[0]) + c * float(v[1]), float(v[2]))
        hits = [j for j, u in enumerate(fv) if max(abs(float(a) - b) for a, b in zip(u, target)) < 1e-9]
        assert len(hits) == 1, (k, i, hits)
        order.append(hits[0])
assert sorted(set(order)) == list(range(62)) and len(order) == 70
pos = {}
for slot, j in enumerate(order):
    pos.setdefault(j, slot)

# The rational model: multiples of 2^-64 (the axis vertices exactly on z).
BITS = 64
def rnd(x): return F(int((x * (1 << BITS)).to_integral_value()), 1 << BITS)
fq = [[rnd(x) for x in v] for v in fv]
for j, v in enumerate(fv):
    if on_axis(v):
        fq[j] = [F(0), F(0), rnd(v[2])]
assert max(sum(x * x for x in v) for v in fq) < 1
err = max(abs(D(q.numerator) / D(q.denominator) - x) for j in range(62) for q, x in zip(fq[j], fv[j]))

with open(out_file, "w") as f:
    f.write("name deltoidalhexecontahedron\nseeds 14\n")
    for slot, j in enumerate(order):
        f.write("vertex %d %s\n" % (slot, " ".join(f"{x:.40f}" for x in fv[j])))
    for slot, j in enumerate(order):
        f.write("rational_vertex %d %s\n" % (slot, " ".join(f"{x.numerator}/{x.denominator}" for x in fq[j])))
    for fc in faces:
        f.write("face %s\n" % " ".join(str(pos[m]) for m in fc))
    for l in passthrough:
        f.write(l + "\n")
print(f"deltoidal hexecontahedron: 62 vertices (70 slots, 2 on the axis x5), 60 kites, "
      f"max |rational - exact| = {float(err):.3e}; wrote {out_file}")
