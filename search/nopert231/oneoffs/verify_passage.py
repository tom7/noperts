# Exact rational check of a candidate near-identity Rupert passage for #229.
# Builds rational Cayley rotations approximating the float witness, then
# checks with Fractions that every projected inner vertex is strictly inside
# the projected outer hull. Prints the worst margin.
# #229-specific: reads #229's vertices229_exact27.json, which lives on branch q
# (branch R carries #231's vertices instead). Run from a checkout of q.
# Usage: python3 oneoffs/verify_passage.py code tri t s wx wy wz theta
import json, math, sys
from fractions import Fraction as F

V = [[F(v[k]) for k in 'xyz'] for v in json.load(open('vertices229_exact27.json'))['vertices']]
Vd = [[float(x) for x in v] for v in V]
bdd = json.load(open('codebdd229.json'))

def vadd(a,b): return [x+y for x,y in zip(a,b)]
def vsc(a,s): return [x*s for x in a]
def vsub(a,b): return [x-y for x,y in zip(a,b)]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
def norm(a): return math.sqrt(dot(a,a))
def unit(a): n=norm(a); return [x/n for x in a]

code, tri, t, s = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
omega = unit([float(x) for x in sys.argv[5:8]])
theta = float(sys.argv[8])
C = [[float(F(x[k])) for k in 'xyz'] for x in bdd['codes'][code]['triangles'][tri]]
e = vadd(C[1], vsc(vsub(C[2], C[1]), t))
u = unit(vadd(e, vsc(vsub(C[0], e), s)))
ax = min(range(3), key=lambda i: abs(u[i])); axis=[0,0,0]; axis[ax]=1
f = unit(cross(u, axis)); g = cross(u, f)
R2 = [f, g, u]
def rod(v, a, th):
    c, sn = math.cos(th), math.sin(th)
    return vadd(vadd(vsc(v, c), vsc(cross(a, v), sn)), vsc(a, dot(a, v)*(1-c)))
# R1 = R2 * Rrod : rows of R1 are rows of R2 applied after rotation: R1 v = R2 (Rrod v)
cols = [rod([1,0,0],omega,theta), rod([0,1,0],omega,theta), rod([0,0,1],omega,theta)]
Rrod = [[cols[j][i] for j in range(3)] for i in range(3)]
R1 = [[sum(R2[i][k]*Rrod[k][j] for k in range(3)) for j in range(3)] for i in range(3)]

def quat(R):
    tr = R[0][0]+R[1][1]+R[2][2]
    w = math.sqrt(max(0,1+tr))/2
    x = (R[2][1]-R[1][2])/(4*w); y = (R[0][2]-R[2][0])/(4*w); z = (R[1][0]-R[0][1])/(4*w)
    return w,x,y,z
def cayleyQ(x,y,z):
    d = 1+x*x+y*y+z*z
    return [[(1+x*x-y*y-z*z)/d, 2*(x*y-z)/d, 2*(x*z+y)/d],
            [2*(x*y+z)/d, (1-x*x+y*y-z*z)/d, 2*(y*z-x)/d],
            [2*(x*z-y)/d, 2*(y*z+x)/d, (1-x*x-y*y+z*z)/d]]
def ratR(R, den):
    w,x,y,z = quat(R)
    p = [F(x/w).limit_denominator(den), F(y/w).limit_denominator(den), F(z/w).limit_denominator(den)]
    return cayleyQ(*p), p
den = 10**16
R1q, p1 = ratR(R1, den); R2q, p2 = ratR(R2, den)

def proj(R, v): return [sum(R[0][k]*v[k] for k in range(3)), sum(R[1][k]*v[k] for k in range(3))]
outer = [proj(R2q, v) for v in V]
inner0 = [proj(R1q, v) for v in V]

def hull(P):
    idx = sorted(range(len(P)), key=lambda i: (P[i][0], P[i][1]))
    def cr(o,a,b): return (P[a][0]-P[o][0])*(P[b][1]-P[o][1])-(P[a][1]-P[o][1])*(P[b][0]-P[o][0])
    lo=[]; 
    for i in idx:
        while len(lo)>=2 and cr(lo[-2],lo[-1],i)<=0: lo.pop()
        lo.append(i)
    up=[]
    for i in reversed(idx):
        while len(up)>=2 and cr(up[-2],up[-1],i)<=0: up.pop()
        up.append(i)
    return lo[:-1]+up[:-1]   # CCW
H = hull(outer)
print('outer hull (exact):', H)
# Float LP for translation: maximize s with s <= (h_e - n_e.(q+t)) / |n|
edges=[]
for i in range(len(H)):
    a, b = outer[H[i]], outer[H[(i+1)%len(H)]]
    n = [float(b[1]-a[1]), float(a[0]-b[0])]  # outward for CCW
    ln = math.hypot(*n); n=[n[0]/ln, n[1]/ln]
    h = n[0]*float(a[0]) + n[1]*float(a[1])
    g_ = h - max(n[0]*float(q[0]) + n[1]*float(q[1]) for q in inner0)
    edges.append((n, g_))
best=(-1e30,None)
import itertools
for (A,B,Cc) in itertools.combinations(range(len(edges)),3):
    M=[[edges[k][0][0],edges[k][0][1],1.0] for k in (A,B,Cc)]; r=[edges[k][1] for k in (A,B,Cc)]
    def det3(m): return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0])
    D=det3(M)
    if abs(D)<1e-14: continue
    x=[]
    for col in range(3):
        m2=[[r[i] if j==col else M[i][j] for j in range(3)] for i in range(3)]
        x.append(det3(m2)/D)
    tt=x[:2]
    sv=min(g_-n[0]*tt[0]-n[1]*tt[1] for n,g_ in edges)
    if sv>best[0]: best=(sv,tt)
print('float clearance with rational rotations: %.4e' % best[0])
tq = [F(best[1][0]).limit_denominator(10**18), F(best[1][1]).limit_denominator(10**18)]
inner = [[q[0]+tq[0], q[1]+tq[1]] for q in inner0]
# Exact strict containment: for CCW hull edge (a,b), point p strictly inside iff cross(b-a, p-a) > 0.
worst = None
for i in range(len(H)):
    a, b = outer[H[i]], outer[H[(i+1)%len(H)]]
    L = math.hypot(float(b[0]-a[0]), float(b[1]-a[1]))
    for k,p in enumerate(inner):
        c = (b[0]-a[0])*(p[1]-a[1]) - (b[1]-a[1])*(p[0]-a[0])
        if worst is None or c < worst[0]: worst = (c, k, H[i], H[(i+1)%len(H)], float(c)/L)
print('EXACT worst cross product: %.6e (inner vertex %d vs outer edge %d-%d), signed distance %.4e' % (float(worst[0]), worst[1], worst[2], worst[3], worst[4]))
print('STRICTLY INSIDE (exact, rationalVertices):', worst[0] > 0)
print('Cayley params inner:', [str(x) for x in p1])
print('Cayley params outer:', [str(x) for x in p2])
print('translation:', [str(x) for x in tq])
