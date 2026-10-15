#!/usr/bin/env python3
"""Cross-check the pentagonal hexecontahedron model against an independent
construction.

ph-model.txt builds the solid as the polar dual of the snub dodecahedron
(snub-model.txt). cc-lib's PentagonalHexecontahedron() (geom/polyhedra.cc)
instead uses David McCooey's closed-form coordinates
(https://dmccooey.com/polyhedra/LpentagonalHexecontahedron.txt), in terms of
the real root x of x^3 = 2x + phi (Cardano's formula below). This
script recomputes McCooey's 92 vertices to 60 digits, scales both solids to
unit circumradius, and searches for an orthogonal map (a rotation, possibly
composed with a reflection) taking one vertex set onto the other. It reports
the largest vertex mismatch, which should be at the precision of the model
file (40 digits).

Usage: python3 ph-crosscheck.py [ph-model.txt]
"""

import itertools
import sys
from decimal import Decimal as D, getcontext

getcontext().prec = 60
model_file = sys.argv[1] if len(sys.argv) > 1 else "ph-model.txt"


def cbrt(a):
    # Real cube root by Newton's method.
    neg = a < 0
    a = abs(a)
    r = D(float(a) ** (1 / 3))
    for _ in range(200):
        r = r - (r * r * r - a) / (3 * r * r)
    return -r if neg else r


def sqrt(a):
    return a.sqrt()


# McCooey's constants, transcribed as in cc-lib geom/polyhedra.cc.
phi = (1 + sqrt(D(5))) / 2
x_term = sqrt(phi - D(5) / 27)
x = cbrt((phi + x_term) / 2) + cbrt((phi - x_term) / 2)
xx = x * x
C = [
    phi * sqrt(3 - xx) / 2,
    phi * sqrt((x - 1 - 1 / x) * phi) / (2 * x),
    phi * sqrt((x - 1 - 1 / x) * phi) / 2,
    xx * phi * sqrt(3 - xx) / 2,
    phi * sqrt(1 - x + (1 + phi) / x) / 2,
    sqrt(x * (x + phi) + 1) / (2 * x),
    sqrt((x + 2) * phi + 2) / (2 * x),
    sqrt(-xx * (2 + phi) + x * (1 + 3 * phi) + 4) / 2,
    (1 + phi) * sqrt(1 + 1 / x) / (2 * x),
    sqrt(2 + 3 * phi - 2 * x + 3 / x) / 2,
    sqrt(xx * (392 + 225 * phi) + x * (249 + 670 * phi) + (470 + 157 * phi)) / 62,
    phi * sqrt(x * (x + phi) + 1) / (2 * x),
    phi * sqrt(xx + x + 1 + phi) / (2 * x),
    phi * sqrt(xx + 2 * x * phi + 2) / (2 * x),
    sqrt(xx * (1 + 2 * phi) - phi) / 2,
    phi * sqrt(xx + x) / 2,
    phi ** 3 * sqrt(x * (x + phi) + 1) / (2 * xx),
    sqrt(xx * (617 + 842 * phi) + x * (919 + 1589 * phi) + (627 + 784 * phi)) / 62,
    phi ** 2 * sqrt(x * (x + phi) + 1) / (2 * x),
    phi * sqrt(x * (x + phi) + 1) / 2,
]
# McCooey's quoted values (to 1e-10, as polyhedra.cc checks).
QUOTED = ["0.192893711352359022108262546061", "0.218483370127321224365534157111",
          "0.374821658114562295266609516608", "0.567715369466921317374872062669",
          "0.728335176957191477360671629838", "0.755467260516595579705585253517",
          "0.824957552676275846265811111988", "0.921228888309550499468934175898",
          "0.959987701391583803994339068107", "1.13706613386050418840961998424",
          "1.16712343647533397917215468549", "1.22237170490362309266282747264",
          "1.27209628257581214613814794036", "1.52770307085850512136921113078",
          "1.64691794069037444140475745697", "1.74618644098582634573474528789",
          "1.86540131081769566577029161408", "1.88844538928366915418351670356",
          "1.97783896542021867236841272616", "2.097053835252087992403959052348"]
for c, q in zip(C, QUOTED):
    assert abs(c - D(q)) < D("1e-28"), (c, q)

Z = D(0)
# The vertex list of polyhedra.cc, as (index or 0, sign) triples.
ROWS = """
-0 -1 -19|-0 1 19|0 1 -19|0 -1 19|-19 -0 -1|-19 0 1|19 0 -1|19 -0 1|-1 -19 -0|-1 19 0|1 19 -0|1 -19 0
z -5 -18|z -5 18|z 5 -18|z 5 18|-18 z -5|-18 z 5|18 z -5|18 z 5|-5 -18 z|-5 18 z|5 -18 z|5 18 z
-10 z -17|-10 z 17|10 z -17|10 z 17|-17 -10 z|-17 10 z|17 -10 z|17 10 z|z -17 -10|z -17 10|z 17 -10|z 17 10
-3 6 -16|-3 -6 16|3 -6 -16|3 6 16|-16 3 -6|-16 -3 6|16 -3 -6|16 3 6|-6 16 -3|-6 -16 3|6 -16 -3|6 16 3
-2 -9 -15|-2 9 15|2 9 -15|2 -9 15|-15 -2 -9|-15 2 9|15 2 -9|15 -2 9|-9 -15 -2|-9 15 2|9 15 -2|9 -15 2
-7 -8 -14|-7 8 14|7 8 -14|7 -8 14|-14 -7 -8|-14 7 8|14 7 -8|14 -7 8|-8 -14 -7|-8 14 7|8 14 -7|8 -14 7
-4 12 -13|-4 -12 13|4 -12 -13|4 12 13|-13 4 -12|-13 -4 12|13 -4 -12|13 4 12|-12 13 -4|-12 -13 4|12 -13 -4|12 13 4
"""


def entry(tok):
    if tok == "z":
        return Z
    neg = tok.startswith("-")
    v = C[int(tok.lstrip("-"))]
    return -v if neg else v


mccooey = []
for row in ROWS.strip().splitlines():
    for t in row.split("|"):
        mccooey.append(tuple(entry(s) for s in t.split()))
for sx in (-1, 1):
    for sy in (-1, 1):
        for sz in (-1, 1):
            mccooey.append((sx * C[11], sy * C[11], sz * C[11]))
assert len(mccooey) == 92

ours = []
seen = set()
for line in open(model_file):
    t = line.split()
    if t and t[0] == "vertex":
        p = tuple(D(s) for s in t[2:5])
        if p not in seen:  # axis vertices are listed in several slots
            seen.add(p)
            ours.append(p)
assert len(ours) == 92, len(ours)


def dot(a, b): return sum(p * q for p, q in zip(a, b))
def norm(a): return dot(a, a).sqrt()
def sub(a, b): return tuple(p - q for p, q in zip(a, b))


def normalize(P):
    c = tuple(sum(p[i] for p in P) / len(P) for i in range(3))
    assert norm(c) < D("1e-35"), norm(c)
    r = max(norm(p) for p in P)
    return [tuple(q / r for q in p) for p in P]


A, B = normalize(ours), normalize(mccooey)


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def inv3(m):
    d = det3(m)
    return [[(m[(j + 1) % 3][(i + 1) % 3] * m[(j + 2) % 3][(i + 2) % 3]
              - m[(j + 1) % 3][(i + 2) % 3] * m[(j + 2) % 3][(i + 1) % 3]) / d
             for j in range(3)] for i in range(3)]


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


# Three of our vertices (a 5-fold vertex and two of its nearest neighbors),
# and every triple of McCooey's with the same norms and mutual distances.
a0 = 0
near = sorted(range(92), key=lambda j: norm(sub(A[j], A[a0])))[1:3]
X = [A[a0], A[near[0]], A[near[1]]]
tol = D("1e-30")
best = None
for t in itertools.permutations(range(92), 3):
    Y = [B[i] for i in t]
    if any(abs(norm(Y[i]) - norm(X[i])) > tol for i in range(3)):
        continue
    if any(abs(norm(sub(Y[i], Y[j])) - norm(sub(X[i], X[j]))) > tol
           for i, j in ((0, 1), (0, 2), (1, 2))):
        continue
    XT = [[X[c][r] for c in range(3)] for r in range(3)]
    YT = [[Y[c][r] for c in range(3)] for r in range(3)]
    M = matmul(YT, inv3(XT))  # M X_c = Y_c
    MA = [tuple(sum(M[r][c] * p[c] for c in range(3)) for r in range(3)) for p in A]
    err = max(min(norm(sub(q, b)) for b in B) for q in MA)
    # A bijection: each of McCooey's vertices is hit.
    hit = {min(range(92), key=lambda j: norm(sub(q, B[j]))) for q in MA}
    orth = max(abs(sum(M[k][i] * M[k][j] for k in range(3)) - (1 if i == j else 0))
               for i in range(3) for j in range(3))
    if len(hit) == 92 and (best is None or err < best[0]):
        best = (err, orth, det3(M), t)
if best is None:
    raise SystemExit("FAILED: no orthogonal map takes the model onto McCooey's vertices")
err, orth, d, t = best
print(f"model {model_file} vs cc-lib/McCooey PentagonalHexecontahedron (both scaled to "
      f"circumradius 1): orthogonal map with det {float(d):+.0f}, "
      f"orthogonality error {float(orth):.1e}, max vertex mismatch {float(err):.1e}")
if err > D("1e-35") or orth > D("1e-35"):
    raise SystemExit("FAILED: mismatch above 1e-35")
print("OK: the same solid up to similarity" +
      (" and a reflection: McCooey's laevo form is the mirror image of the dual of"
       " Wikipedia's snub dodecahedron (and of cc-lib's SnubDodecahedron)" if d < 0 else ""))
