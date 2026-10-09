"""The field K = Q(sqrt5, s), s = sin 72 degrees (s^2 = (5 + sqrt5)/8): exact
arithmetic for the icosahedral solids in the 5-fold frame (snub, PH, DH).

An element is a + b sqrt5 + c s + d s sqrt5 with rational a, b, c, d.
"""

import math
from fractions import Fraction as F

R5 = math.sqrt(5)
S72 = math.sqrt((5 + R5) / 8)


class K:
    __slots__ = ("v",)

    def __init__(self, a=0, b=0, c=0, d=0):
        self.v = (F(a), F(b), F(c), F(d))

    def __add__(x, y):
        if not isinstance(y, K): y = K(y)
        return K(*(p + q for p, q in zip(x.v, y.v)))
    __radd__ = __add__

    def __neg__(x): return K(*(-p for p in x.v))
    def __sub__(x, y): return x + (-(y if isinstance(y, K) else K(y)))
    def __rsub__(x, y): return K(y) - x

    def __mul__(x, y):
        if not isinstance(y, K): y = K(y)
        a, b, c, d = x.v
        e, f, g, h = y.v
        p, q = c * g + 5 * d * h, c * h + d * g
        return K(a * e + 5 * b * f + (5 * p + 5 * q) / 8, a * f + b * e + (p + 5 * q) / 8,
                 a * g + 5 * b * h + c * e + 5 * d * f, a * h + b * g + c * f + d * e)
    __rmul__ = __mul__

    def __eq__(x, y):
        if not isinstance(y, K): y = K(y)
        return x.v == y.v

    def __hash__(x): return hash(x.v)
    def is_zero(x): return all(q == 0 for q in x.v)
    def f(x): return float(x.v[0]) + float(x.v[1]) * R5 + float(x.v[2]) * S72 + float(x.v[3]) * R5 * S72

    def inv(x):
        a, b, c, d = x.v
        A, B = K(a, b), K(c, d)
        s2 = K(F(5, 8), F(1, 8))
        n = A * A - B * B * s2
        na, nb = n.v[0], n.v[1]
        den = na * na - 5 * nb * nb
        return (A - B * K(0, 0, 1)) * K(na / den, -nb / den)

    def __truediv__(x, y): return x * (y.inv() if isinstance(y, K) else K(F(1) / F(y)))

    def sign(x):
        """Exact sign: 0 iff all coefficients are 0; otherwise refine an enclosure."""
        if x.is_zero(): return 0
        val = x.f()
        if abs(val) > 1e-9: return 1 if val > 0 else -1
        raise ValueError("sign of a tiny nonzero element: refine (not needed so far)")

    def ser(x): return " ".join(f"{q.numerator}/{q.denominator}" for q in x.v)

    @staticmethod
    def parse(tokens):
        return K(*(F(t) for t in tokens))


def dot(a, b): return sum((p * q for p, q in zip(a, b)), K())
def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
def sub(a, b): return [p - q for p, q in zip(a, b)]
def scale(a, s): return [p * s for p in a]
def fvec(a): return [p.f() for p in a]
def is_zero_vec(a): return all(p.is_zero() for p in a)

ZERO = K()
ONE = K(1)
SQRT5 = K(0, 1)
S = K(0, 0, 1)
C72 = K(F(-1, 4), F(1, 4))


def mm(x, y):
    return tuple(tuple(sum((x[i][k] * y[k][j] for k in range(3)), K()) for j in range(3)) for i in range(3))


def matvec(m, v):
    return [sum((m[i][k] * v[k] for k in range(3)), K()) for i in range(3)]


def ico_group():
    """The 60 rotations in ico_group.py's (and Lean's icoEntry) order."""
    I = tuple(tuple(ONE if i == j else ZERO for j in range(3)) for i in range(3))
    RZ = ((C72, -S, ZERO), (S, C72, ZERO), (ZERO, ZERO, ONE))
    RX = ((ONE, ZERO, ZERO), (ZERO, -ONE, ZERO), (ZERO, ZERO, -ONE))
    sin_t, cos_t = K(0, F(2, 5)), K(0, F(1, 5))
    cos_a, sin_a = K(0, 0, F(-1, 2), F(1, 2)), K(F(1, 4), F(1, 4))
    n = (sin_t * cos_a, sin_t * sin_a, cos_t)
    cr = ((ZERO, -n[2], n[1]), (n[2], ZERO, -n[0]), (-n[1], n[0], ZERO))
    T = tuple(tuple((C72 if i == j else ZERO) + S * cr[i][j] + (ONE - C72) * n[i] * n[j] for j in range(3))
              for i in range(3))
    group, index = [I], {I: 0}
    i = 0
    while i < len(group):
        for g in (RZ, RX, T):
            h = mm(group[i], g)
            if h not in index:
                index[h] = len(group)
                group.append(h)
        i += 1
    assert len(group) == 60
    return group
