#!/usr/bin/env python3
"""leaf2cert.py: turns capcert-m12 --leaflog files of cap 3 (frame P) into Lean certificate trees.
Usage: leaf2cert.py out.txt U|WP leaf1.txt [leaf2.txt ...]   (U: the 52 U charts, WP: the 26 wedge charts)
Output: for every required chart (U sides 0..3 x 13 kinds, WP 26 charts) `chart <id>` and a preorder tree
(`s axis`, `l ...`, `c`) rebuilt from the leaves: an axis not straddled by any leaf is split; a box without leaves is `c`
(left to Lean's coneOk). Root boxes as in Pipeline/ArcCap.lean (P parameters below).
Chart ids (ArcCapDecode.parseId): `chart u <n> <kind> <ax> <sg>` with n = 1,2,3,0 for the sides 0,1,2,3; `chart p <kind> ...`."""
import sys
import numpy as np
from fractions import Fraction as F
sys.setrecursionlimit(10000)
MU0, R, S = 0.125, 0.5, 2.0
NU0, R1, R2, R3, Z = 1.0, 2.0, 2.0, 16.0, 8.0
def ubox(kind, ax):
    if kind == 'fe': return [(0, MU0), (-1, 1), (-R, R), (-R, R), (-S, S)]
    rng = [R, R, S]
    if kind == 'face':
        fr = [i for i in range(3) if i != ax]
        return [(0, MU0), (-1, 1), (0, 1), (-rng[fr[0]], rng[fr[0]]), (-rng[fr[1]], rng[fr[1]])]
    return [(0, MU0), (-1, 1), (0, 1), (-1, 1), (-1, 1)]
NU, T = (0, NU0), (0, 1)
def pbox(name):
    if name.startswith('Fp'): return [NU, T, (0, 1), (-1, 1), (-1, 1)]
    if name.startswith('face0'): return [NU, T, (-1, 1), (-R2, R2), (-R3, R3)]
    if name.startswith('face1'): return [NU, T, (-1, 1), (-R1, R1), (-R3, R3)]
    if name.startswith('face2I'): return [NU, T, (-1, 1), (-Z, Z), (-Z, Z)]
    if name.startswith('face2_1'): return [NU, T, (-1, 1), (0, R1), (-R2, R2)]
    if name.startswith('face2_2'): return [NU, T, (-1, 1), (-Z, Z), (0, R2)]
    raise Exception(name)
sidecode = {0: 1, 1: 2, 2: 3, 3: 0}
charts = []  # (name, id line, box)
for side in range(4):
    charts.append((f'U{side}:Fe', f'chart pu {sidecode[side]} 0 0 0', ubox('fe', 0)))
    for ax in range(3):
        for sg in '+-':
            b = 1 if sg == '+' else 0
            charts.append((f'U{side}:face{ax}{sg}', f'chart pu {sidecode[side]} 1 {ax} {b}', ubox('face', ax)))
            charts.append((f'U{side}:cone{ax}{sg}', f'chart pu {sidecode[side]} 2 {ax} {b}', ubox('cone', ax)))
for al in '+-':
    ab = 1 if al == '+' else 0
    for k in range(3):
        for sg in '+-':
            b = 1 if sg == '+' else 0
            charts.append((f'WP:Fp{al}{k}{sg}', f'chart p 0 {ab} {k} {b}', pbox('Fp')))
for sg in '+-':
    b = 1 if sg == '+' else 0
    charts.append((f'WP:face0{sg}', f'chart p 1 {b}', pbox('face0')))
    charts.append((f'WP:face1{sg}', f'chart p 2 {b}', pbox('face1')))
    for m, nm in enumerate(['I', '_1P', '_1M', '_2P', '_2M']):
        charts.append((f'WP:face2{nm}{sg}', f'chart p 3 {m} {b}', pbox('face2' + nm)))

def leafline(rest):
    # rest: after the name and 10 numbers: "| n a b ... s | S0 , S1 , | j.. i.. ; ..."
    p = rest.split('|')
    h = p[1].split(); n = int(h[0]); s = int(h[-1]); ch = [(int(h[1 + 2 * k]), int(h[2 + 2 * k])) for k in range(n)]
    Ss = [[int(v) for v in g.split()] for g in p[2].split(',')[:n]]
    res = {}
    for tup in p[3].split(';'):
        v = tup.split()
        if not v: continue
        v = [int(x) for x in v]
        res[tuple(v[:n])] = v[3:3 + n]
    out = [f'l {n} {s}']
    for k in range(n):
        out.append(f'{ch[k][0]} {ch[k][1]} {len(Ss[k])} ' + ' '.join(map(str, Ss[k])))
    ntup = 1
    for k in range(n): ntup *= len(Ss[k])
    out.append(str(ntup))
    def emit(k, jj):
        if k < 0:
            return [str(x) for x in res[tuple(jj)]]
        r = []
        for v in Ss[k]:
            jj[k] = v
            r += emit(k - 1, jj)
        return r
    out += emit(n - 1, [0] * n)
    return ' '.join(out)

data = {}
want = sys.argv[2]
charts = [c for c in charts if c[0].startswith(want + ('' if want == 'WP' else ''))]
for fn in sys.argv[3:]:
    for line in open(fn):
        name, rest = line.split(' ', 1)
        nums = rest.split('|')[0].split()
        assert len(nums) == 10
        box = [float(x) for x in nums]
        data.setdefault(name, []).append((box, leafline('|' + rest.split('|', 1)[1].rstrip('\n'))))

out = open(sys.argv[1], 'w')
for name, idline, root in charts:
    L = data.get(name, [])
    lo = np.array([[b[2 * i] for i in range(5)] for b, _ in L]).reshape(-1, 5)
    hi = np.array([[b[2 * i + 1] for i in range(5)] for b, _ in L]).reshape(-1, 5)
    texts = [t for _, t in L]
    out.write(idline + '\n')
    nleaf = 0
    def rec(idx, box):
        global nleaf
        if len(idx) == 0:
            out.write('c\n'); return
        l = lo[idx]; h = hi[idx]
        if len(idx) == 1 and all(l[0][i] == box[i][0] and h[0][i] == box[i][1] for i in range(5)):
            out.write(texts[idx[0]] + '\n'); nleaf += 1; return
        for a in range(5):
            mid = (box[a][0] + box[a][1]) / 2
            st = (l[:, a] < mid) & (h[:, a] > mid)
            if not st.any():
                out.write(f's {a}\n')
                lw = idx[h[:, a] <= mid]; up = idx[l[:, a] >= mid]
                b1 = list(box); b1[a] = (box[a][0], mid)
                rec(lw, b1)
                b2 = list(box); b2[a] = (mid, box[a][1])
                rec(up, b2)
                return
        raise Exception(f'{name}: no split axis, {len(idx)} leaves in {box}')
    rec(np.arange(len(L)), root)
    assert nleaf == len(L), (name, nleaf, len(L))
out.close()
