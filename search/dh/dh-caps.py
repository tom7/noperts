#!/usr/bin/env python3
"""Writes the 5D search's caps file (search5d --caps) for the deltoidal
hexecontahedron: each capcert cap (u0, ux) and its images under the
rotation group and central symmetry (the pose (u, R) is a passage iff
(g u, g R g^-1) is, and u and -u give the same shadow).

One line per cap: x e1 e2 (9 doubles), mu0, wmax (doubles), then the exact
frame (9 coordinates, each a b c d: a + b sqrt5 + c s + d s sqrt5 with
s = sin 72) and mu0, wmax^2 as rationals. The base frames are the 'kframe'
lines of `capcert.exe --cap u0|ux [--aniso] --frame_only`.

Usage: dh-caps.py MU0 WMAX frame_u0.txt frame_ux.txt > caps.txt"""
import sys
from fractions import Fraction as F
from kfield import K, ico_group

mu0, wmax = F(sys.argv[1]), F(sys.argv[2])
G = ico_group()
seen = set()
for path in sys.argv[3:]:
    toks = next(l.split()[1:] for l in open(path) if l.startswith('kframe '))
    assert len(toks) == 36
    ks = [K(*map(F, toks[4 * i:4 * i + 4])) for i in range(9)]
    v = [ks[3 * i:3 * i + 3] for i in range(3)]
    for g in G:
        for s in (1, -1):
            img = [[sum((g[i][k] * a[k] for k in range(3)), K()) * s for i in range(3)] for a in v]
            key = tuple(c.v for a in img for c in a)
            if key in seen: continue
            seen.add(key)
            dbl = ' '.join('%.17g' % c.f() for a in img for c in a)
            ex = ' '.join(str(q) for a in img for c in a for q in c.v)
            print(dbl, '%.17g %.17g' % (float(mu0), float(wmax)), ex, mu0, wmax * wmax)
