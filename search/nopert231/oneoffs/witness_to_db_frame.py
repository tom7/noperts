# Convert a near-identity passage for Lean's #229 frame into the solution-DB
# frame of nopert_229 (DB = Lean / s, rotated about z by phi), check it
# exactly against the DB vertices, and print FrameStrings.
# Usage: python3 witness_to_db_frame.py code tri t s wx wy wz theta
import sqlite3, json, math, sys, itertools, subprocess
from fractions import Fraction as F
sys.path.insert(0, '.')
N229 = '/root/quad/nopert229'
db = sqlite3.connect('file:/root/quad/ruperts/ruperts.sqlite?mode=ro', uri=True)
vv = [float(x) for x in db.execute("select vertices from noperts where id=229").fetchone()[0].split(',')]
D = [vv[i:i+3] for i in range(0, 60, 3)]
L = [[float(F(x[k])) for k in 'xyz'] for x in json.load(open(N229 + '/vertices229_exact27.json'))['vertices']]
s_scale = max(math.sqrt(sum(a*a for a in p)) for p in L) / max(math.sqrt(sum(a*a for a in p)) for p in D)
# phi: rotate DB about z so that DB*s matches Lean.
def rz(p, a): c, s = math.cos(a), math.sin(a); return [c*p[0]-s*p[1], s*p[0]+c*p[1], p[2]]
best = None
for d in D:
    if abs(d[2]*s_scale - L[0][2]) > 1e-6: continue
    phi = math.atan2(L[0][1], L[0][0]) - math.atan2(d[1], d[0])
    err = max(min(max(abs(a*s_scale - b) for a, b in zip(rz(dd, phi), l)) for dd in D) for l in L)
    if best is None or err < best[0]: best = (err, phi)
err, phi = best
print('# scale %.15f phi %.15f max vertex mismatch %.2e' % (s_scale, phi, err), file=sys.stderr)

# Reproduce the witness rotations (same construction as rupert_witness229.py).
code, tri, t, s = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
omega = [float(x) for x in sys.argv[5:8]]; n = math.sqrt(sum(x*x for x in omega)); omega = [x/n for x in omega]
theta = float(sys.argv[8])
def cross(a,b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def unit(a): m = math.sqrt(dot(a,a)); return [x/m for x in a]
bdd = json.load(open(N229 + '/codebdd229.json'))
C = [[float(F(x[k])) for k in 'xyz'] for x in bdd['codes'][code]['triangles'][tri]]
e = [C[1][i] + t*(C[2][i]-C[1][i]) for i in range(3)]
u = unit([e[i] + s*(C[0][i]-e[i]) for i in range(3)])
ax = min(range(3), key=lambda i: abs(u[i])); axis = [0,0,0]; axis[ax] = 1
f = unit(cross(u, axis)); g = cross(u, f)
R2 = [f, g, u]
def rod(v, a, th):
    c, sn = math.cos(th), math.sin(th); ca = cross(a, v); d = dot(a, v)*(1-c)
    return [v[i]*c + ca[i]*sn + a[i]*d for i in range(3)]
cols = [rod([1,0,0],omega,theta), rod([0,1,0],omega,theta), rod([0,0,1],omega,theta)]
Rrod = [[cols[j][i] for j in range(3)] for i in range(3)]
R1 = [[sum(R2[i][k]*Rrod[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
c, sn = math.cos(phi), math.sin(phi)
Rz = [[c, -sn, 0], [sn, c, 0], [0, 0, 1]]
def mm(A, B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
O = mm(R2, Rz); I = mm(R1, Rz)   # applied to DB vertices (up to the scale)

def proj(M, p): return [sum(M[r][k]*p[k] for k in range(3)) for r in range(2)]
outer = [proj(O, d) for d in D]; inner0 = [proj(I, d) for d in D]
def hull(P):
    idx = sorted(range(len(P)), key=lambda i: (P[i][0], P[i][1]))
    def cr(o,a,b): return (P[a][0]-P[o][0])*(P[b][1]-P[o][1])-(P[a][1]-P[o][1])*(P[b][0]-P[o][0])
    lo=[]
    for i in idx:
        while len(lo)>=2 and cr(lo[-2],lo[-1],i)<=0: lo.pop()
        lo.append(i)
    up=[]
    for i in reversed(idx):
        while len(up)>=2 and cr(up[-2],up[-1],i)<=0: up.pop()
        up.append(i)
    return lo[:-1]+up[:-1]
H = hull(outer)
edges = []
for i in range(len(H)):
    a, b = outer[H[i]], outer[H[(i+1)%len(H)]]
    nn = [b[1]-a[1], a[0]-b[0]]; ln = math.hypot(*nn); nn = [nn[0]/ln, nn[1]/ln]
    h = nn[0]*a[0] + nn[1]*a[1]
    edges.append((nn, h - max(nn[0]*q[0] + nn[1]*q[1] for q in inner0)))
def det3(m): return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0])
bestc = (-1e30, None)
for trip in itertools.combinations(range(len(edges)), 3):
    M = [[edges[k][0][0], edges[k][0][1], 1.0] for k in trip]; r = [edges[k][1] for k in trip]
    Dt = det3(M)
    if abs(Dt) < 1e-14: continue
    x = [det3([[r[i] if j == col else M[i][j] for j in range(3)] for i in range(3)])/Dt for col in range(3)]
    sv = min(g_ - nn[0]*x[0] - nn[1]*x[1] for nn, g_ in edges)
    if sv > bestc[0]: bestc = (sv, x[:2])
clr, tr = bestc
# Exact check with the double values as rationals.
Oq = [[F(x) for x in row] for row in O]; Iq = [[F(x) for x in row] for row in I]
Dq = [[F(x) for x in p] for p in D]; tq = [F(tr[0]), F(tr[1])]
oq = [proj(Oq, p) for p in Dq]; iq = [[a+b for a, b in zip(proj(Iq, p), tq)] for p in Dq]
Hq = hull(oq)
worst = min((oq[Hq[(i+1)%len(Hq)]][0]-oq[Hq[i]][0])*(p[1]-oq[Hq[i]][1]) - (oq[Hq[(i+1)%len(Hq)]][1]-oq[Hq[i]][1])*(p[0]-oq[Hq[i]][0])
            for i in range(len(Hq)) for p in iq)
print('# float clearance %.4e, exact min cross %.4e -> %s' % (clr, float(worst), 'OK' if worst > 0 else 'FAIL'), file=sys.stderr)
if worst <= 0: sys.exit(1)
def frame_string(M, o):
    cols = [[M[r][c] for r in range(3)] for c in range(3)]
    vals = cols[0] + cols[1] + cols[2] + o
    return ','.join('%.17g' % v for v in vals)
print(frame_string(O, [0.0, 0.0, 0.0]))
print(frame_string(I, [tr[0], tr[1], 0.0]))
print('%.17g' % clr)
