#!/usr/bin/env python3
"""The pentagonal hexecontahedron's model file (for codebdd --model_file).

The pentagonal hexecontahedron is the polar dual of the snub dodecahedron:
its 92 vertices are the poles n/d of the snub's 92 face planes n.x = d, and
its 60 faces (pentagons) are dual to the snub's vertices (face of v: the
plane v.x = 1, through the poles of the 5 snub faces at v).

- The exact solid: the dual of the exact snub (snub_model.txt, 40 digits).
- The rational model: the dual of a high-precision rational snub (rounded to
  2^-64, pentagons snapped exactly planar). Every pentagon of the dual is then
  EXACTLY planar (the poles of the faces at a snub vertex v all satisfy
  v.x = 1), which no independent rounding of the 92 vertices could achieve,
  since each vertex lies on 3 or 5 faces.
- Both are scaled by the same rational factor so that the largest vertex has
  norm just below 1 (Lean's GoodPoly invariant).
- Frame: the snub's (z a 5-fold axis, x a 2-fold axis). Vertex S k + s is seed
  s rotated by 2 pi k / 5 (S = 20 seeds). Two vertices lie ON the z axis; the
  C5 orbit of each is a single point, listed 5 times (exact copies), so that
  the C5 indexing (Fin 5 x seeds) still applies.

Lines written: name, seeds, vertex i x y z (the exact solid, 40 digits),
rational_vertex i p/q p/q p/q (the model, exact), face ..., view_triangle,
neighbor (copied from the snub).

Usage: python3 ph_model.py [snub=snub_model.txt] [out=ph_model.txt]
"""

import itertools
import math
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

getcontext().prec = 80
snub_file = sys.argv[1] if len(sys.argv) > 1 else "snub_model.txt"
out_file = sys.argv[2] if len(sys.argv) > 2 else "ph_model.txt"

lines = open(snub_file).read().splitlines()
snub_x = []  # exact snub, unit circumradius
snub_faces5 = []
passthrough = []
for l in lines:
    t = l.split()
    if not t:
        continue
    if t[0] == "vertex":
        snub_x.append(tuple(Decimal(x) for x in t[2:5]))
    elif t[0] == "face":
        snub_faces5.append([int(x) for x in t[1:]])
    elif t[0] in ("view_triangle", "neighbor"):
        passthrough.append(l)
assert len(snub_x) == 60 and len(snub_faces5) == 12


def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def cross(a, b): return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])
def dot(a, b): return sum(x * y for x, y in zip(a, b))


# The snub's faces (float detection, exact afterwards): 80 triangles, 12 pentagons.
fl = [tuple(float(x) for x in v) for v in snub_x]
faces = []
seen = set()
for i, j, k in itertools.combinations(range(60), 3):
    nv = cross(sub(fl[j], fl[i]), sub(fl[k], fl[i]))
    if math.sqrt(dot(nv, nv)) < 1e-9:
        continue
    d = dot(nv, fl[i])
    vals = [dot(nv, v) - d for v in fl]
    if max(vals) > 1e-9 and min(vals) < -1e-9:
        continue
    fs = frozenset(m for m in range(60) if abs(vals[m]) < 1e-9)
    if fs not in seen:
        seen.add(fs)
        faces.append(sorted(fs))
assert len(faces) == 92, len(faces)
assert sorted(len(f) for f in faces).count(5) == 12

# The rational snub: round to 2^-64, then snap each pentagon planar (its
# vertices after the first three onto the plane through those, along the
# normal). Each snub vertex is in exactly one pentagon, so each moves at most
# once; the two horizontal pentagons (one C5 orbit each) are planar as rounded.
BITS = 64


def rnd(x):
    return F(int((x * (1 << BITS)).to_integral_value()), 1 << BITS)


snub_q = [tuple(rnd(x) for x in v) for v in snub_x]
for f in snub_faces5:
    a, b, c = (snub_q[m] for m in f[:3])
    nv = cross(sub(b, a), sub(c, a))
    nn = dot(nv, nv)
    for m in f[3:]:
        p = snub_q[m]
        t = (dot(nv, p) - dot(nv, a)) / nn
        snub_q[m] = tuple(x - t * y for x, y in zip(p, nv))
    assert all(dot(nv, snub_q[m]) == dot(nv, a) for m in f)


def pole(verts, f):
    a, b, c = (verts[m] for m in f[:3])
    nv = cross(sub(b, a), sub(c, a))
    d = dot(nv, a)
    if d < 0:
        nv, d = tuple(-x for x in nv), -d
    assert all(dot(nv, verts[m]) == d for m in f) or not isinstance(d, F)
    return tuple(x / d for x in nv)


ph_q = [pole(snub_q, f) for f in faces]
ph_x = [pole(snub_x, f) for f in faces]

# Every PH face (dual to snub vertex v) is exactly planar: v.x = 1 for the
# poles of the faces at v.
for v in range(60):
    assert all(dot(snub_q[v], ph_q[i]) == 1 for i, f in enumerate(faces) if v in f)

# Scale so that the largest vertex has norm just below 1 - 1e-9.
rmax = max(math.sqrt(float(dot(p, p))) for p in ph_q)
scale = F(int((1 - 1e-9) / rmax * (1 << 40)), 1 << 40)
ph_q = [tuple(scale * x for x in p) for p in ph_q]
ph_x = [tuple(Decimal(scale.numerator) / Decimal(scale.denominator) * x for x in p) for p in ph_x]
assert max(dot(p, p) for p in ph_q) < 1

# C5 order: seeds have azimuth in [0, 72) degrees (axis vertices: azimuth 0),
# sorted by decreasing z; vertex S k + s is seed s rotated by 2 pi k / 5.
def az(v): return math.atan2(float(v[1]), float(v[0])) % (2 * math.pi)
def on_axis(v): return abs(float(v[0])) < 1e-30 and abs(float(v[1])) < 1e-30
seeds = [i for i, v in enumerate(ph_x) if on_axis(v) or az(v) < 2 * math.pi / 5 - 1e-12]
assert len(seeds) == 20, len(seeds)
seeds.sort(key=lambda i: (-float(ph_x[i][2]), az(ph_x[i])))
c72, s72 = math.cos(2 * math.pi / 5), math.sin(2 * math.pi / 5)


def rot(k, v):
    c, s = math.cos(2 * math.pi * k / 5), math.sin(2 * math.pi * k / 5)
    return (c * v[0] - s * v[1], s * v[0] + c * v[1], v[2])


order = []
for k in range(5):
    for s in seeds:
        target = rot(k, [float(x) for x in ph_x[s]])
        hits = [i for i, v in enumerate(ph_x) if max(abs(float(a) - b) for a, b in zip(v, target)) < 1e-9]
        assert len(hits) == 1, (k, s, hits)
        order.append(hits[0])
assert sorted(set(order)) == list(range(92)) and len(order) == 100
for i, j in enumerate(order):
    if on_axis(ph_x[j]):
        assert j == order[i % 20]  # an axis vertex: the same point in every orbit

err = max(abs(Decimal(q.numerator) / Decimal(q.denominator) - x)
          for i in range(92) for q, x in zip(ph_q[i], ph_x[i]))
print(f"pentagonal hexecontahedron: 92 vertices (100 slots, 2 on the axis x5), 60 planar pentagons, "
      f"scale {float(scale):.6f}, max |rational - exact| = {float(err):.3e}, "
      f"max bits {max(max(x.numerator.bit_length(), x.denominator.bit_length()) for p in ph_q for x in p)}")

pos = {j: i for i, j in enumerate(order)}  # first slot of each vertex
with open(out_file, "w") as f:
    f.write("name pentagonalhexecontahedron\nseeds 20\n")
    for i, j in enumerate(order):
        f.write("vertex %d %s\n" % (i, " ".join(f"{x:.40f}" for x in ph_x[j])))
    for i, j in enumerate(order):
        f.write("rational_vertex %d %s\n" % (i, " ".join(f"{x.numerator}/{x.denominator}" for x in ph_q[j])))
    for v in range(60):
        f.write("face %s\n" % " ".join(str(pos[i]) for i, fc in enumerate(faces) if v in fc))
    for l in passthrough:
        f.write(l + "\n")
print("wrote", out_file)
