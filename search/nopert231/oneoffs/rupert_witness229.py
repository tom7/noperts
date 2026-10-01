# Generate (and exactly pre-check) Lean witness data for a near-identity
# Rupert passage of Nopert #229, in the format of
# Noperthedron/Nopert229/RupertWitness.lean (RationalChecks over tightVertex).
# Usage: python3 oneoffs/rupert_witness229.py code tri t s wx wy wz theta
# #229-specific: reads #229's vertices229_exact27.json, which lives on branch q
# (branch R carries #231's vertices instead). Run from a checkout of q.
import json, math, sys, itertools
from fractions import Fraction as F

Vj = json.load(open('vertices229_exact27.json'))['vertices']
seed = [[F(Vj[s][k]) for k in 'xyz'] for s in range(4)]
cos72 = F(30901699437494745, 10**17); sin72 = F(9510565162951535, 10**16)
cos144 = 2*cos72**2 - 1; sin144 = 2*sin72*cos72
TC = [F(1), cos72, cos144, cos144, cos72]; TS = [F(0), sin72, sin144, -sin144, -sin72]
def tight(i):
    k, s = i // 4, i % 4; c, sn = TC[k], TS[k]; v = seed[s]
    return [c*v[0] - sn*v[1], sn*v[0] + c*v[1], v[2]]
V = [tight(i) for i in range(20)]
bdd = json.load(open('codebdd229.json'))

def vadd(a,b): return [x+y for x,y in zip(a,b)]
def vsc(a,s): return [x*s for x in a]
def vsub(a,b): return [x-y for x,y in zip(a,b)]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
def unit(a): n=math.sqrt(dot(a,a)); return [x/n for x in a]

code, tri, t, s = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
omega = unit([float(x) for x in sys.argv[5:8]]); theta = float(sys.argv[8])
C = [[float(F(x[k])) for k in 'xyz'] for x in bdd['codes'][code]['triangles'][tri]]
e = vadd(C[1], vsc(vsub(C[2], C[1]), t))
u = unit(vadd(e, vsc(vsub(C[0], e), s)))
ax = min(range(3), key=lambda i: abs(u[i])); axis=[0,0,0]; axis[ax]=1
f = unit(cross(u, axis)); g = cross(u, f)
R2 = [f, g, u]
def rod(v, a, th):
    c, sn = math.cos(th), math.sin(th)
    return vadd(vadd(vsc(v, c), vsc(cross(a, v), sn)), vsc(a, dot(a, v)*(1-c)))
cols = [rod([1,0,0],omega,theta), rod([0,1,0],omega,theta), rod([0,0,1],omega,theta)]
Rrod = [[cols[j][i] for j in range(3)] for i in range(3)]
R1 = [[sum(R2[i][k]*Rrod[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def quat(R):
    tr = R[0][0]+R[1][1]+R[2][2]; w = math.sqrt(max(0,1+tr))/2
    return w, (R[2][1]-R[1][2])/(4*w), (R[0][2]-R[2][0])/(4*w), (R[1][0]-R[0][1])/(4*w)
def cayleyQ(x,y,z):
    d = 1+x*x+y*y+z*z
    return [[(1+x*x-y*y-z*z)/d, 2*(x*y-z)/d, 2*(x*z+y)/d],
            [2*(x*y+z)/d, (1-x*x+y*y-z*z)/d, 2*(y*z-x)/d],
            [2*(x*z-y)/d, 2*(y*z+x)/d, (1-x*x-y*y+z*z)/d]]
def params(R, den=10**12):
    w,x,y,z = quat(R)
    return [F(x/w).limit_denominator(den), F(y/w).limit_denominator(den), F(z/w).limit_denominator(den)]
p1 = params(R1); p2 = params(R2)
R1q = cayleyQ(*p1); R2q = cayleyQ(*p2)
def proj(R, v): return [sum(R[j][k]*v[k] for k in range(3)) for j in range(2)]
outer = [proj(R2q, v) for v in V]
inner0 = [proj(R1q, v) for v in V]

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
# Translation by float LP (max-min clearance), then rationalized.
edges=[]
for i in range(len(H)):
    a, b = outer[H[i]], outer[H[(i+1)%len(H)]]
    n = [float(b[1]-a[1]), float(a[0]-b[0])]; ln = math.hypot(*n); n=[n[0]/ln, n[1]/ln]
    h = n[0]*float(a[0]) + n[1]*float(a[1])
    edges.append((n, h - max(n[0]*float(q[0]) + n[1]*float(q[1]) for q in inner0)))
def det3(m): return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0])
best=(-1e30,None)
for trip in itertools.combinations(range(len(edges)),3):
    M=[[edges[k][0][0],edges[k][0][1],1.0] for k in trip]; r=[edges[k][1] for k in trip]
    D=det3(M)
    if abs(D)<1e-14: continue
    x=[det3([[r[i] if j==col else M[i][j] for j in range(3)] for i in range(3)])/D for col in range(3)]
    sv=min(g_-n[0]*x[0]-n[1]*x[1] for n,g_ in edges)
    if sv>best[0]: best=(sv,x[:2])
off = [F(best[1][0]).limit_denominator(10**15), F(best[1][1]).limit_denominator(10**15)]
inner = [[q[0]+off[0], q[1]+off[1]] for q in inner0]
print('-- float clearance %.4e; outer hull %s' % (best[0], H), file=sys.stderr)

def crossQ2(p,a,b): return (a[0]-p[0])*(b[1]-p[1]) - (a[1]-p[1])*(b[0]-p[0])
dQ = F(2, 10**16)
tris=[]; worst=None
for i,p in enumerate(inner):
    bt=None
    for a,b,c in itertools.combinations(H,3):
        # orient CCW
        if crossQ2(outer[a],outer[b],outer[c]) < 0: b,c = c,b
        m = min(crossQ2(p,outer[b],outer[c]), crossQ2(p,outer[c],outer[a]), crossQ2(p,outer[a],outer[b]))
        if bt is None or m > bt[0]: bt=(m,(a,b,c))
    tris.append(bt[1])
    ok = bt[0] > 40*dQ and all(abs(x)<=2 for x in p) and all(abs(x)<=2 for v in bt[1] for x in outer[v])
    if worst is None or bt[0] < worst: worst = bt[0]
    if not ok: print('-- FAIL vertex', i, float(bt[0]), file=sys.stderr)
print('-- worst min crossQ2 = %.4e (need > %.1e)' % (float(worst), float(40*dQ)), file=sys.stderr)
print('-- ALL RationalChecks pass (exact):', worst > 40*dQ, file=sys.stderr)
def q(x): return ('%d' % x.numerator) if x.denominator == 1 else ('%d / %d' % (x.numerator, x.denominator))
print('def cx₁ : ℚ := %s' % q(p1[0])); print('def cy₁ : ℚ := %s' % q(p1[1])); print('def cz₁ : ℚ := %s' % q(p1[2]))
print('def cx₂ : ℚ := %s' % q(p2[0])); print('def cy₂ : ℚ := %s' % q(p2[1])); print('def cz₂ : ℚ := %s' % q(p2[2]))
print('def offsetQ : Fin 2 → ℚ :=\n  ![%s, %s]' % (q(off[0]), q(off[1])))
print('def witnessTriangle : Fin 20 → Fin 20 × Fin 20 × Fin 20 := ![\n  ' +
      ',\n  '.join(', '.join('(%d, %d, %d)' % tris[5*r+c] for c in range(5)) for r in range(4)) + ']')
