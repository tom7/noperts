#!/usr/bin/env python3
# Idealized #231: exact C5 symmetry and exactly planar quads (notes/IDEAL231.md).
# Reads Lean's seeds and rationalVertices from Noperthedron's Vertices.lean,
# computes the planar seed z1* in closed form, and checks the quads' planarity
# and every vertex's distance to rationalVertices, with 120-digit decimals.
#
# Usage: oneoffs/ideal231.py [path/to/Vertices.lean]
import itertools, re, sys
from decimal import Decimal as D, getcontext
from fractions import Fraction as F

getcontext().prec = 120
path = sys.argv[1] if len(sys.argv) > 1 else \
    '/root/quad/Noperthedron/Noperthedron/Nopert229/Vertices.lean'
src = open(path).read()

def rows(name):
  start = src.index(f'def {name}')
  block = src[start:src.index(']\n\n', start)]
  return [[F(x) for x in re.findall(r'-?\d+/\d+|-?\d+(?![\d/])', row)]
          for row in re.findall(r'!\[([^\[\]]+)\]', block)]

def dec(f): return D(f.numerator) / D(f.denominator)

seeds = rows('seedVertex')        # Lean seed order s = 0..3
rational = rows('rationalVertices')
assert len(seeds) == 4 and len(rational) == 20

r5 = D(5).sqrt()
c = (r5 - 1) / 4                  # cos 72°
s = (D(10) + 2 * r5).sqrt() / 4   # sin 72°
cos_k = [D(1), c, 2 * c * c - 1, 2 * c * c - 1, c]
sin_k = [D(0), s, 2 * s * c, -2 * s * c, -s]

def rot(k, p):
  x, y, z = p
  return (cos_k[k] * x - sin_k[k] * y, sin_k[k] * x + cos_k[k] * y, z)

S = [tuple(map(dec, p)) for p in seeds]
x2, y2, z2 = S[2]
a1, b1, z1 = S[1]
# d = R^-1 s2 - s2 (no z part), e = s3 - s2; quad {s1, s2, s3, R^-1 s2}.
dx, dy = (c - 1) * x2 + s * y2, -s * x2 + (c - 1) * y2
ex, ey, ez = (S[3][i] - S[2][i] for i in range(3))
z1_star = z2 - ez * (-dy * (a1 - x2) + dx * (b1 - y2)) / (ex * dy - ey * dx)

ideal = list(S)
ideal[1] = (a1, b1, z1_star)
V = [rot(k, ideal[j]) for k in range(5) for j in range(4)]
E = [rot(k, S[j]) for k in range(5) for j in range(4)]  # Lean's exactVertex

def sub(p, q): return tuple(u - v for u, v in zip(p, q))
def cross(p, q): return (p[1]*q[2]-p[2]*q[1], p[2]*q[0]-p[0]*q[2], p[0]*q[1]-p[1]*q[0])
def dot(p, q): return sum(u * v for u, v in zip(p, q))
def norm(p): return dot(p, p).sqrt()

def quad_defect(W, q):
  worst = D(0)
  for tri in itertools.combinations(q, 3):
    other = (set(q) - set(tri)).pop()
    n = cross(sub(W[tri[1]], W[tri[0]]), sub(W[tri[2]], W[tri[0]]))
    worst = max(worst, abs(dot(n, sub(W[other], W[tri[0]]))) / norm(n))
  return worst

quads = [[(4 * k + j) % 20 for j in (1, 2, 3)] + [(4 * k + 18) % 20] for k in range(5)]
print('z1  (Lean seed)  =', f'{z1:.40f}')
print('z1* (planar)     =', f'{z1_star:.40f}')
print('z1* - z1         = %.6e' % (z1_star - z1))
for q in quads:
  print('quad', sorted(q), 'defect: exactVerts %.3e, ideal %.1e'
        % (quad_defect(E, q), quad_defect(V, q)))
R = [tuple(map(dec, r)) for r in rational]
print('max |exactVertex - rationalVertex| = %.4e' % max(norm(sub(E[i], R[i])) for i in range(20)))
print('max |idealVertex - rationalVertex| = %.4e  (checker allowance 6e-16)'
      % max(norm(sub(V[i], R[i])) for i in range(20)))
print('ideal seeds (40 digits):')
for j, p in enumerate(ideal):
  print(f'  s{j} = (' + ', '.join(f'{u:.40f}' for u in p) + ')')
