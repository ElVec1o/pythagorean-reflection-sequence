# m=8 stratum: extract the 15 depth-10 coincidence pairs (vs the Coxeter
# reference W_8) at two exact leg samples, then verify each identically in the
# legs over Q(c), c = 2cos(pi/8) -- whole-stratum certificate, no sympy.
# Also: word-level check that no coincidence occurs before depth 10.
# Arithmetic: NF = Q[c]/(c^4-4c^2+2); affine group over K = NF + s*NF,
# s = sin(pi/8), s^2 = 1 - c^2/4; polynomials in (a,b) with K-coefficients.
from fractions import Fraction as Fr
import time, resource
from collections import defaultdict

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**30

MP = [Fr(2), Fr(0), Fr(-4), Fr(0)]      # x^4 = -(2 - 4x^2) = 4x^2 - 2
DEG = 4
class NF:
    __slots__ = ("c",)
    def __init__(s, c): s.c = tuple(c)
    @classmethod
    def const(cls, v): return cls((Fr(v), Fr(0), Fr(0), Fr(0)))
    @classmethod
    def gen(cls): return cls((Fr(0), Fr(1), Fr(0), Fr(0)))
    def __add__(a, b): return NF(tuple(x+y for x, y in zip(a.c, b.c)))
    def __sub__(a, b): return NF(tuple(x-y for x, y in zip(a.c, b.c)))
    def __neg__(a): return NF(tuple(-x for x in a.c))
    def __bool__(a): return any(a.c)
    def __eq__(a, b): return a.c == b.c
    def __hash__(a): return hash(a.c)
    def __mul__(a, b):
        full = [Fr(0)]*7
        for i, x in enumerate(a.c):
            if x:
                for j, y in enumerate(b.c):
                    if y: full[i+j] += x*y
        for k in (6, 5, 4):
            co = full[k]
            if co:
                full[k] = Fr(0)
                for i in range(DEG): full[k-DEG+i] -= co*MP[i]
        return NF(tuple(full[:DEG]))
    def inv(a):
        cols = []
        basis = NF.const(1)
        g = NF.gen()
        for i in range(DEG):
            cols.append((a*basis).c)
            basis = basis*g
        M = [[cols[c][r] for c in range(DEG)] + [Fr(1) if r == 0 else Fr(0)]
             for r in range(DEG)]
        for col in range(DEG):
            piv = next(r for r in range(col, DEG) if M[r][col] != 0)
            M[col], M[piv] = M[piv], M[col]
            pv = M[col][col]
            M[col] = [x/pv for x in M[col]]
            for r in range(DEG):
                if r != col and M[r][col]:
                    f = M[r][col]
                    M[r] = [x - f*y for x, y in zip(M[r], M[col])]
        return NF(tuple(M[r][DEG] for r in range(DEG)))

class K2:   # u + v s, s^2 = S2
    __slots__ = ("u", "v")
    def __init__(s, u, v): s.u = u; s.v = v
    @classmethod
    def const(cls, x): return cls(NF.const(x), NF.const(0))
    def __add__(a, b): return K2(a.u+b.u, a.v+b.v)
    def __sub__(a, b): return K2(a.u-b.u, a.v-b.v)
    def __neg__(a): return K2(-a.u, -a.v)
    def __bool__(a): return bool(a.u) or bool(a.v)
    def __eq__(a, b): return a.u == b.u and a.v == b.v
    def __hash__(a): return hash((a.u, a.v))
    def __mul__(a, b):
        return K2(a.u*b.u + a.v*b.v*S2, a.u*b.v + a.v*b.u)
    def inv(a):
        n = (a.u*a.u - a.v*a.v*S2).inv()
        return K2(a.u*n, -(a.v*n))

C = NF.gen()
COSNF = C*NF.const(Fr(1, 2))
S2 = NF.const(1) - COSNF*COSNF
COS = K2(COSNF, NF.const(0))
SIN = K2(NF.const(0), NF.const(1))
assert (COS*COS + SIN*SIN) == K2.const(1)

def affine_gens(a, b):
    O = K2.const(0); I = K2.const(1)
    def refl(p0, d):
        L = d[0]*d[0] + d[1]*d[1]
        Li = L.inv()
        m11 = (d[0]*d[0] - d[1]*d[1])*Li
        m12 = (K2.const(2)*d[0]*d[1])*Li
        tx = p0[0] - (m11*p0[0] + m12*p0[1])
        ty = p0[1] - (m12*p0[0] - m11*p0[1])
        return (m11, m12, m12, -m11, tx, ty)
    V0 = (K2.const(a), O); V1 = (K2.const(b)*COS, K2.const(b)*SIN)
    return [(I, O, O, -I, O, O),
            refl((O, O), (COS, SIN)),
            refl(V0, (V1[0]-V0[0], V1[1]-V0[1]))]

def cox_gens():
    O = NF.const(0); I = NF.const(1)
    B = [[I, -COSNF, -I], [-COSNF, I, -I], [-I, -I, I]]
    gens = []
    for i in range(3):
        M = []
        for r in range(3):
            row = []
            for c in range(3):
                v = I if r == c else O
                if r == i: v = v - NF.const(2)*B[i][c]
                row.append(v)
            M.append(tuple(row))
        gens.append(tuple(M))
    return gens

def amul6(g, h):
    return (g[0]*h[0]+g[1]*h[2], g[0]*h[1]+g[1]*h[3],
            g[2]*h[0]+g[3]*h[2], g[2]*h[1]+g[3]*h[3],
            g[0]*h[4]+g[1]*h[5]+g[4], g[2]*h[4]+g[3]*h[5]+g[5])
def mmul3(X, Y):
    return tuple(tuple(X[i][0]*Y[0][j] + X[i][1]*Y[1][j] + X[i][2]*Y[2][j]
                       for j in range(3)) for i in range(3))

def extract(a, b, dmax=10):
    G = affine_gens(a, b)
    W = cox_gens()
    for g in G:
        gg = amul6(g, g)
        assert gg == (K2.const(1), K2.const(0), K2.const(0), K2.const(1),
                      K2.const(0), K2.const(0)), "not an involution"
    IG = (K2.const(1), K2.const(0), K2.const(0), K2.const(1), K2.const(0), K2.const(0))
    IW = tuple(tuple(NF.const(1) if i == j else NF.const(0) for j in range(3))
               for i in range(3))
    front = [("", IG, IW)]
    pairs = None
    for d in range(1, dmax+1):
        new = []
        for (w, Mg, Mw) in front:
            last = int(w[-1]) if w else -1
            for i in range(3):
                if i == last: continue
                new.append((w+str(i), amul6(Mg, G[i]), mmul3(Mw, W[i])))
        front = new
        byg = defaultdict(dict)
        for (w, Mg, Mw) in front:
            byg[Mg].setdefault(Mw, w)
        extra = [sorted(v.values()) for v in byg.values() if len(v) > 1]
        print(f"   legs ({a},{b}) d={d:2d}: words {len(front):5d}, "
              f"extra classes {len(extra):3d}  [rss {rss_gb():.2f}GB]", flush=True)
        assert rss_gb() < 4.0
        if d < dmax: assert not extra, f"coincidence before depth {dmax}"
        else:
            assert len(extra) == 15 and all(len(e) == 2 for e in extra)
            pairs = sorted(tuple(e) for e in extra)
    return pairs

print("PHASE 1: extraction at two samples")
p1 = extract(1, 2)
p2 = extract(2, 3)
assert p1 == p2, "pair sets differ between samples"
print(f"   identical 15 word pairs at both samples:")
for w1, w2 in p1: print(f"      {w1} == {w2}")

# ---------- PHASE 2: polynomial identity over Q(c)[a,b] ----------
# reflections as homogeneous 3x3 matrices with polynomial entries times 1/L:
# mirror 0: L=1; mirror 1 (through origin, direction (cos,sin)): L=1;
# mirror 2 (through (a,0) and b(cos,sin)): L = (b cos - a)^2 + (b sin)^2.
# Entries live in Q(c)[a,b]: polys = dict {(i,j): K2-coeff}.
print("\nPHASE 2: identities over Q(c)[a,b]")
def pmul(A, B):
    r = {}
    for (i1, j1), c1 in A.items():
        for (i2, j2), c2 in B.items():
            k = (i1+i2, j1+j2)
            v = r.get(k)
            v = c1*c2 if v is None else v + c1*c2
            if v: r[k] = v
            elif k in r: del r[k]
    return r
def padd(A, B):
    r = dict(A)
    for k, c in B.items():
        v = r.get(k)
        v = c if v is None else v + c
        if v: r[k] = v
        elif k in r: del r[k]
    return r
def kconst(x): return {(0, 0): x} if x else {}
PA = {(1, 0): K2.const(1)}   # a
PB = {(0, 1): K2.const(1)}   # b
ONEP = kconst(K2.const(1))

def mm(X, Y):
    return [[padd(padd(pmul(X[i][0], Y[0][j]), pmul(X[i][1], Y[1][j])),
                  pmul(X[i][2], Y[2][j])) for j in range(3)] for i in range(3)]

# mirror 0: y -> -y
A0 = [[ONEP, {}, {}], [{}, kconst(K2.const(-1)), {}], [{}, {}, ONEP]]
L0 = ONEP
# mirror 1: reflection across direction (cos,sin) through origin:
# S = [[cos2t, sin2t],[sin2t, -cos2t]], cos2t = 2cos^2-1, sin2t = 2 sin cos
c2t = K2.const(2)*COS*COS - K2.const(1)
s2t = K2.const(2)*SIN*COS
A1 = [[kconst(c2t), kconst(s2t), {}], [kconst(s2t), kconst(-c2t), {}], [{}, {}, ONEP]]
L1 = ONEP
# mirror 2: through (a,0), direction d = (b cos - a, b sin); L = dx^2 + dy^2
dx = padd({(0, 1): COS}, {(1, 0): K2.const(-1)})
dy = {(0, 1): SIN}
L2 = padd(pmul(dx, dx), pmul(dy, dy))
a2 = padd(pmul(dx, dx), {k: -v for k, v in pmul(dy, dy).items()})
b2 = {k: K2.const(2)*v for k, v in pmul(dx, dy).items()}
# t = (I-S) p0, p0 = (a, 0):  L*tx = (L - a2)*a ; L*ty = -b2*a
t2x = pmul(padd(L2, {k: -v for k, v in a2.items()}), PA)
t2y = pmul({k: -v for k, v in b2.items()}, PA)
A2 = [[a2, b2, t2x], [b2, {k: -v for k, v in a2.items()}, t2y], [{}, {}, L2]]
AM = [A0, A1, A2]; LM = [L0, L1, L2]
I3 = [[ONEP, {}, {}], [{}, ONEP, {}], [{}, {}, ONEP]]

def wmat(w):
    M, l = I3, ONEP
    for ch in w:
        i = int(ch)
        M = mm(M, AM[i]); l = pmul(l, LM[i])
    return M, l

t0 = time.time(); ok = 0
for w1, w2 in p1:
    M1, l1 = wmat(w1)
    M2, l2 = wmat(w2)
    good = all(pmul(M1[i][j], l2) == pmul(M2[i][j], l1)
               for i in range(3) for j in range(3))
    ok += good
    if not good: print(f"   FAIL: {w1} vs {w2}")
    assert rss_gb() < 4.0
print(f"   {ok}/15 pairs hold identically in Q(c)[a,b]  "
      f"[{time.time()-t0:.0f}s, rss {rss_gb():.2f}GB]")
assert ok == 15
print("\n=> the m=8 row (d*,delta) = (10,15) holds on the whole stratum: onset "
      "by the identities, exactness off a proper closed subset by the samples")
