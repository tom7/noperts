#!/usr/bin/env python3
"""Exact data for the deltoidal hexecontahedron's tie tubes (tietube.cc).

A pinning plane x^perp holds an antipodal pair of 5-fold and of 2-fold
vertices; the reflection sigma_x maps the DH K to L = sigma_x K, whose shadow
along views u in a wedge from x lies inside K's and touches it. The pose
R = H_u S H_x (H the half-turns) is a passage iff S L's shadow fits strictly
inside K's (central symmetry). tietube.cc certifies small S by witnesses:
an L-vertex q at a touching point and an edge direction c of K through it
(d = u x c), with (N(w) q - D(w) v_j) . d >= 0 for every vertex j of K.

This script computes, exactly over K = Q(sqrt5, sin 72) (kfield.py), for the
pinning normals x' = g x (g in I) whose wedge can meet the view triangle T:
the vertices of L, which of them equal a vertex of K or lie inside an edge of
K (exact), and the witness candidates (q, c) with their tied vertices j
(q - v_j parallel to c, exactly: the w^0 term of their polynomial vanishes).

Writes dh_tie_data.txt:
  V j <x> <y> <z>                 K's distinct vertices (each coordinate: 4 rationals)
  X n <x> <y> <z>                 pinning normal n (unnormalized)
  L n i <x> <y> <z>               L_n's vertex i (= sigma_x v_i)
  W n i <cx> <cy> <cz> tied j...  witness: L_n vertex i, direction c
Usage: python3 dh_tie_data.py [exact=dh_exact.txt] [out=dh_tie_data.txt] [max_deg=25]
"""

import math
import sys
from fractions import Fraction as F

from kfield import K, dot, cross, sub, scale, fvec, is_zero_vec, ico_group, matvec

exact = sys.argv[1] if len(sys.argv) > 1 else "dh_exact.txt"
out = sys.argv[2] if len(sys.argv) > 2 else "dh_tie_data.txt"
max_deg = float(sys.argv[3]) if len(sys.argv) > 3 else 25.0

slots, x0 = {}, None
for line in open(exact):
    t = line.split()
    if not t or t[0].startswith("#"): continue
    if t[0] == "kvertex":
        slots[int(t[1])] = [K.parse(t[2 + 4 * k: 6 + 4 * k]) for k in range(3)]
    elif t[0] == "pinning":
        x0 = [K.parse(t[1 + 4 * k: 5 + 4 * k]) for k in range(3)]
V, slot_v = [], {}
for s in sorted(slots):
    p = slots[s]
    j = next((k for k, q in enumerate(V) if all((a - b).is_zero() for a, b in zip(p, q))), None)
    if j is None:
        j = len(V)
        V.append(p)
    slot_v[s] = j
assert len(V) == 62
def unit(v): n = math.sqrt(sum(c * c for c in v)); return [c / n for c in v]
edges = set()
for line in open("dh_model.txt"):
    t = line.split()
    if t and t[0] == "face":
        f = sorted({slot_v[int(s)] for s in t[1:]})
        # Faces are listed by sorted index: order them cyclically around the centroid.
        P = [fvec(V[j]) for j in f]
        cen = [sum(p[c] for p in P) / len(P) for c in range(3)]
        nrm = unit(cen)
        e1 = unit([P[0][c] - cen[c] for c in range(3)])
        e2 = [nrm[1] * e1[2] - nrm[2] * e1[1], nrm[2] * e1[0] - nrm[0] * e1[2], nrm[0] * e1[1] - nrm[1] * e1[0]]
        f.sort(key=lambda j: math.atan2(sum((fvec(V[j])[c] - cen[c]) * e2[c] for c in range(3)),
                                        sum((fvec(V[j])[c] - cen[c]) * e1[c] for c in range(3))))
        for k in range(len(f)):
            edges.add(tuple(sorted((f[k], f[(k + 1) % len(f)]))))
assert len(edges) == 120, len(edges)
nbrs = {j: [] for j in range(len(V))}
for a, b in edges:
    nbrs[a].append(b)
    nbrs[b].append(a)

# The view triangle T (the model's chamber), as unit vectors for the distance test.
T = [[0, 0, 1], [500 / 1343, 160 / 1343, 683 / 1343], [250 / 1281, 345 / 1281, 686 / 1281]]
def unit(v): n = math.sqrt(sum(c * c for c in v)); return [c / n for c in v]
Tsamples = []
for i in range(41):
    for j in range(41 - i):
        l = [i / 40, j / 40, 1 - i / 40 - j / 40]
        Tsamples.append(unit([sum(l[k] * T[k][c] for k in range(3)) for c in range(3)]))

group = ico_group()
lines_seen, normals = [], []
for g in group:
    x = matvec(g, x0)
    xf = unit(fvec(x))
    if any(abs(sum(a * b for a, b in zip(xf, y))) > 1 - 1e-12 for y in lines_seen):
        continue
    lines_seen.append(xf)
    dist = min(math.degrees(math.acos(min(1, abs(sum(a * b for a, b in zip(xf, u)))))) for u in Tsamples)
    if dist <= max_deg:
        # Orient toward T.
        if sum(a * b for a, b in zip(xf, Tsamples[len(Tsamples) // 2])) < 0:
            x = scale(x, K(-1))
        normals.append((x, dist))
print(f"{len(lines_seen)} pinning lines; {len(normals)} within {max_deg} deg of T: "
      + ", ".join(f"{d:.1f}" for _, d in normals))

with open(out, "w") as f:
    for j, v in enumerate(V):
        f.write(f"V {j} " + "  ".join(c.ser() for c in v) + "\n")
    for n, (x, dist) in enumerate(normals):
        f.write(f"X {n} " + "  ".join(c.ser() for c in x) + "\n")
        xx = dot(x, x)
        L = [sub(v, scale(x, dot(v, x) * 2 / xx)) for v in V]
        pinned = sum(1 for v in V if dot(v, x).is_zero())
        touch_v, touch_e = 0, 0
        nw = 0
        for i, q in enumerate(L):
            f.write(f"L {n} {i} " + "  ".join(c.ser() for c in q) + "\n")
            eq = [j for j, v in enumerate(V) if is_zero_vec(sub(q, v))]
            cands = []
            if eq:
                touch_v += 1
                j0 = eq[0]
                cands = [sub(V[k], V[j0]) for k in nbrs[j0]]
            else:
                for a, b in edges:
                    e = sub(V[b], V[a])
                    if is_zero_vec(cross(sub(q, V[a]), e)):
                        t = (dot(sub(q, V[a]), e) / dot(e, e)).f()
                        if 0 < t < 1:
                            touch_e += 1
                            cands.append(e)
            for c in cands:
                tied = [j for j, v in enumerate(V) if is_zero_vec(cross(sub(q, v), c))]
                f.write(f"W {n} {i} " + "  ".join(cc.ser() for cc in c) + " tied " + " ".join(map(str, tied)) + "\n")
                nw += 1
        print(f"  normal {n} ({dist:.1f} deg from T): {pinned} pinned, {touch_v} L-vertices on K-vertices, "
              f"{touch_e} on K-edges, {nw} witnesses")
print(f"wrote {out}")

# tie_normals.h: the half-turns H_x = 2 x x^T / |x|^2 - I, rounded to 10^-12
# (error <= 5 * 10^-13 per entry), for the 5D search's tie leaves.
from decimal import Decimal as Dd, getcontext
getcontext().prec = 60
r5d, s72d = Dd(5).sqrt(), ((5 + Dd(5).sqrt()) / 8).sqrt()
def kdec(k): return sum((Dd(q.numerator) / Dd(q.denominator)) * m for q, m in zip(k.v, (Dd(1), r5d, s72d, r5d * s72d)))
with open("tie_normals.h", "w") as f:
    f.write("// Generated by dh_tie_data.py: the half-turns H_x = 2 x x^T / |x|^2 - I about the\n"
            "// deltoidal hexecontahedron's pinning normals (dh_tie_data.txt order), entries\n"
            "// rounded to the nearest multiple of 10^-12 (error <= 5 * 10^-13).\n")
    f.write("#ifndef _NOPERT_TIE_NORMALS_H\n#define _NOPERT_TIE_NORMALS_H\n\n#include <cstdint>\n\n")
    f.write(f"inline constexpr int NUM_TIE_NORMALS = {len(normals)};\n")
    f.write("inline constexpr int64_t TIE_HALF_TURN_DENOM = 1000000000000;\n")
    f.write("// Row-major numerators.\ninline constexpr int64_t TIE_HALF_TURN_NUM[NUM_TIE_NORMALS][9] = {\n")
    for x, _ in normals:
        xx = dot(x, x)
        row = []
        for i in range(3):
            for j in range(3):
                h = x[i] * x[j] * 2 / xx - (K(1) if i == j else K())
                n = int((kdec(h) * 10 ** 12).to_integral_value())
                assert abs(Dd(n) / 10 ** 12 - kdec(h)) <= Dd(5) / 10 ** 13
                row.append(n)
        f.write("  {" + ", ".join(map(str, row)) + "},\n")
    f.write("};\n\n#endif\n")
print("wrote tie_normals.h")
