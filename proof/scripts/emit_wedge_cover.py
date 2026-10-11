#!/usr/bin/env python3
"""Helpers for emit_septopert_view_cover.py: exact rational geometry and the
builder of a decision tree certifying that code triangles cover a base
triangle.

The tree is over half-spaces u . a >= 0 for points u on the affine plane
u0 + u1 + u2 = 1:

  * split n pos neg : branch on u . n >= 0 (pos) / u . n <= 0 (neg);
  * empty lam kappa : sum_k lam_k a_k + kappa (1,1,1) = 0 with lam >= 0,
                      kappa > 0 (no point of the plane satisfies the path);
  * leaf t certs    : for each edge functional e_i of code triangle t
                      (oriented so that the triangle is where all are >= 0),
                      e_i = sum_k mu_k a_k + kappa (1,1,1), mu, kappa >= 0.

Here a_k are the path constraints: the three edge functionals of the base
triangle followed by the split normals (with sign) from the root. The Lean
side checks the tree (Septopert/ViewCover.lean for the Septopert's view
domains, on the plane of each projective root; Pipeline/WedgeCover.lean for
the other solids, whose generators are in search/).

The tree is built by exact polygon clipping: the current cell is a convex
polygon in the plane; if it is empty we emit `empty`; if some code triangle
contains it we emit `leaf`; otherwise we split on an edge plane of a code
triangle that cuts the cell.
"""

from __future__ import annotations

import itertools
from fractions import Fraction as F

S = (F(1), F(1), F(1))


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def scale(c, a):
    return (c * a[0], c * a[1], c * a[2])


def neg(a):
    return (-a[0], -a[1], -a[2])


def primitive(v):
    """Positive multiple of v with coprime integer coordinates."""
    from math import gcd, lcm
    den = 1
    for x in v:
        den = lcm(den, x.denominator)
    ints = [int(x * den) for x in v]
    g = 0
    for x in ints:
        g = gcd(g, abs(x))
    return tuple(F(x // g) for x in ints)


def det3(a, b, c):
    return dot(a, cross(b, c))


def edges(tri):
    """Edge functionals e_i with u . e_i = det(...) so that the triangle is
    {u : all u . e_i >= 0} (after orienting by the sign of det)."""
    c0, c1, c2 = tri
    D = det3(c0, c1, c2)
    assert D != 0
    sgn = 1 if D > 0 else -1
    es = [cross(c1, c2), cross(c2, c0), cross(c0, c1)]
    return [scale(F(sgn), e) for e in es]


def clip(poly, a):
    """Clip a convex polygon (list of points on the plane) by u . a >= 0."""
    out = []
    n = len(poly)
    for i in range(n):
        p, q = poly[i], poly[(i + 1) % n]
        dp, dq = dot(p, a), dot(q, a)
        if dp >= 0:
            out.append(p)
        if (dp > 0 and dq < 0) or (dp < 0 and dq > 0):
            t = dp / (dp - dq)
            out.append(add(p, scale(t, sub(q, p))))
    # Remove consecutive duplicates.
    res = []
    for p in out:
        if not res or res[-1] != p:
            res.append(p)
    if len(res) > 1 and res[0] == res[-1]:
        res.pop()
    return res


def solve3(cols, target):
    """Solve sum_j x_j cols[j] = target for 1..3 columns (exact), or None."""
    k = len(cols)
    # Least-squares-free: pick k independent rows by trying row subsets.
    for rows in itertools.combinations(range(3), k):
        M = [[cols[j][r] for j in range(k)] for r in rows]
        rhs = [target[r] for r in rows]
        # Gaussian elimination
        A = [row[:] + [rhs[i]] for i, row in enumerate(M)]
        ok = True
        for c in range(k):
            piv = next((r for r in range(c, k) if A[r][c] != 0), None)
            if piv is None:
                ok = False
                break
            A[c], A[piv] = A[piv], A[c]
            for r in range(k):
                if r != c and A[r][c] != 0:
                    f = A[r][c] / A[c][c]
                    A[r] = [x - f * y for x, y in zip(A[r], A[c])]
        if not ok:
            continue
        x = [A[i][k] / A[i][i] for i in range(k)]
        # verify all 3 coordinates
        chk = (F(0), F(0), F(0))
        for j in range(k):
            chk = add(chk, scale(x[j], cols[j]))
        if chk == tuple(target):
            return x
    return None


def cone_coeffs(gens, target):
    """Find nonnegative coefficients c (len(gens)) with sum c_j gens[j] = target,
    using at most 3 generators (Caratheodory). gens includes S as the last
    generator. Returns None if not found."""
    if all(x == 0 for x in target):
        return [F(0)] * len(gens)
    idx = range(len(gens))
    for k in (1, 2, 3):
        for sub_idx in itertools.combinations(idx, k):
            x = solve3([gens[j] for j in sub_idx], target)
            if x is not None and all(v >= 0 for v in x):
                c = [F(0)] * len(gens)
                for j, v in zip(sub_idx, x):
                    c[j] = v
                return c
    return None


def empty_witness(cons):
    """lam >= 0 over cons and kappa > 0 with sum lam_k a_k + kappa S = 0."""
    # Equivalent: -S in cone(cons) with kappa = 1.
    c = cone_coeffs(cons, neg(S))
    if c is None:
        return None
    return c, F(1)


class Builder:
    def __init__(self, tris):
        self.tris = tris
        self.tri_edges = [edges(t) for t in tris]
        planes = []
        seen = set()
        for es in self.tri_edges:
            for e in es:
                # normalize direction up to positive scale for dedup
                g = max(abs(x) for x in e)
                key = tuple(x / g for x in e)
                nkey = tuple(-x for x in key)
                if key not in seen and nkey not in seen:
                    seen.add(key)
                    planes.append(e)
        self.planes = planes
        self.nodes = 0

    def inside(self, t, poly):
        return all(dot(p, e) >= 0 for e in self.tri_edges[t] for p in poly)

    def build(self, cons, poly, depth=0):
        self.nodes += 1
        gens = cons + [S]
        if len(poly) == 0:
            w = empty_witness(cons)
            assert w is not None, "empty cell without witness"
            lam, kappa = w
            return ("empty", lam[:len(cons)], kappa)
        # Leaf: a triangle containing the whole (closed) cell.
        for t in range(len(self.tris)):
            if self.inside(t, poly):
                certs = []
                for e in self.tri_edges[t]:
                    c = cone_coeffs(gens, e)
                    if c is None:
                        break
                    certs.append((c[:len(cons)], c[len(cons)]))
                if len(certs) == 3:
                    return ("leaf", t, certs)
        # Split on a plane that cuts the cell (vertices strictly on both sides).
        best = None
        for n in self.planes:
            vals = [dot(p, n) for p in poly]
            if min(vals) < 0 < max(vals):
                # prefer balanced splits
                pos = sum(1 for v in vals if v > 0)
                negc = sum(1 for v in vals if v < 0)
                score = min(pos, negc)
                if best is None or score > best[0]:
                    best = (score, n)
        assert best is not None, (f"no splitting plane at depth {depth}: uncovered cell "
                                  f"{[tuple(float(x) for x in p) for p in poly]}")
        n = primitive(best[1])
        pos = self.build(cons + [n], clip(poly, n), depth + 1)
        negn = self.build(cons + [neg(n)], clip(poly, neg(n)), depth + 1)
        return ("split", n, pos, negn)


def q(x: F) -> str:
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    return f"({x.numerator} / {x.denominator} : ℚ)"


def vec(v) -> str:
    return "![" + ", ".join(q(x) for x in v) + "]"


def qlist(xs) -> str:
    return "[" + ", ".join(q(x) for x in xs) + "]"


def emit_node(node, out, defs, counter, structure=None):
    """Emit nodes as separate defs (to keep terms shallow); returns name.
    `structure` collects (name, normal, pos, neg) for splits and (name,) for
    the other nodes, children first."""
    kind = node[0]
    counter[0] += 1
    name = f"node_{counter[0]}"
    if kind == "empty":
        _, lam, kappa = node
        defs.append(f"def {name} : Node := .empty {qlist(lam)} {q(kappa)}")
        if structure is not None:
            structure.append((name,))
    elif kind == "leaf":
        _, t, certs = node
        cs = ", ".join(f"({qlist(m)}, {q(k)})" for m, k in certs)
        defs.append(f"def {name} : Node := .leaf {t} [{cs}]")
        if structure is not None:
            structure.append((name,))
    else:
        _, n, pos, negn = node
        pn = emit_node(pos, out, defs, counter, structure)
        nn = emit_node(negn, out, defs, counter, structure)
        defs.append(f"def {name} : Node := .split {vec(n)} {pn} {nn}")
        if structure is not None:
            structure.append((name, n, pn, nn))
    return name
