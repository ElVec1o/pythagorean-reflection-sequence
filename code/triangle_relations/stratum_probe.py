# Probe m=8 and m=9 (the next orders beyond 7): first deficit of the actual
# group against the Coxeter reference W_m, at sample leg shapes, depth <= 12.
# Non-crystallographic prediction: first deficit at d=11 (the universal 33).
# Exact arithmetic in K = Q(c)(s), c = 2cos(pi/m) with its minimal polynomial,
# s = sin(pi/m), s^2 = 1 - c^2/4 in Q(c). Memory-careful: hashed keys, RSS guard.
from fractions import Fraction as Fr
import hashlib, time, resource, math

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**30

MINPOLY = {8: [2, 0, -4, 0, 1],      # x^4 - 4x^2 + 2  (x = 2cos(pi/8))
           9: [-1, -3, 0, 1],        # x^3 - 3x - 1    (x = 2cos(pi/9))
           10: [5, 0, -5, 0, 1],     # x^4 - 5x^2 + 5  (x = 2cos(pi/10))
           12: [1, 0, -4, 0, 1]}     # x^4 - 4x^2 + 1  (x = 2cos(pi/12))
for m, mp in MINPOLY.items():
    x = 2*math.cos(math.pi/m)
    v = sum(co*x**i for i, co in enumerate(mp))
    assert abs(v) < 1e-9, f"minimal polynomial wrong for m={m}"

class NF:  # element of Q[x]/(minpoly), coeffs tuple of Fractions
    __slots__ = ("c",)
    MP = None; DEG = None
    def __init__(s, c): s.c = tuple(c)
    @classmethod
    def const(cls, v): return cls((Fr(v),) + (Fr(0),)*(cls.DEG-1))
    @classmethod
    def gen(cls): return cls((Fr(0), Fr(1)) + (Fr(0),)*(cls.DEG-2))
    def __add__(a, b): return type(a)(tuple(x+y for x, y in zip(a.c, b.c)))
    def __sub__(a, b): return type(a)(tuple(x-y for x, y in zip(a.c, b.c)))
    def __neg__(a): return type(a)(tuple(-x for x in a.c))
    def __mul__(a, b):
        d = a.DEG
        full = [Fr(0)]*(2*d-1)
        for i, x in enumerate(a.c):
            if not x: continue
            for j, y in enumerate(b.c):
                if y: full[i+j] += x*y
        # reduce: x^d = -(mp[0] + mp[1] x + ...)/mp[d]  (monic assumed)
        for k in range(2*d-2, d-1, -1):
            co = full[k]
            if co:
                full[k] = Fr(0)
                for i in range(d):
                    full[k-d+i] -= co*a.MP[i]
        return type(a)(tuple(full[:d]))
    def inv(a):
        # solve (mult-by-a) x = 1 by Gaussian elimination over Q
        d = a.DEG
        cols = []
        e = type(a)((Fr(1),) + (Fr(0),)*(d-1))
        basis = e
        for i in range(d):
            cols.append((a*basis).c)
            # shift basis by one power of the generator
            gen = type(a)((Fr(0), Fr(1)) + (Fr(0),)*(d-2))
            basis = basis*gen
        # matrix M with M[r][c] = cols[c][r]; solve M x = e1
        M = [[cols[c][r] for c in range(d)] + [Fr(1) if r == 0 else Fr(0)]
             for r in range(d)]
        for col in range(d):
            piv = next(r for r in range(col, d) if M[r][col] != 0)
            M[col], M[piv] = M[piv], M[col]
            pv = M[col][col]
            M[col] = [x/pv for x in M[col]]
            for r in range(d):
                if r != col and M[r][col]:
                    f = M[r][col]
                    M[r] = [x - f*y for x, y in zip(M[r], M[col])]
        return type(a)(tuple(M[r][d] for r in range(d)))
    def key(a): return a.c
    def isz(a): return all(x == 0 for x in a.c)

def make_nf(m):
    mp = MINPOLY[m]
    d = len(mp)-1
    class F(NF): pass
    F.MP = [Fr(x) for x in mp[:-1]]   # monic: coefficients below x^d
    assert mp[-1] == 1
    F.DEG = d
    return F

class K2:  # u + v*s, s^2 = S2 in F
    __slots__ = ("u", "v")
    S2 = None; F = None
    def __init__(s, u, v): s.u = u; s.v = v
    @classmethod
    def const(cls, x): return cls(cls.F.const(x), cls.F.const(0))
    def __add__(a, b): return type(a)(a.u+b.u, a.v+b.v)
    def __sub__(a, b): return type(a)(a.u-b.u, a.v-b.v)
    def __neg__(a): return type(a)(-a.u, -a.v)
    def __mul__(a, b):
        return type(a)(a.u*b.u + a.v*b.v*a.S2, a.u*b.v + a.v*b.u)
    def inv(a):
        n = (a.u*a.u - a.v*a.v*a.S2).inv()
        return type(a)(a.u*n, -(a.v*n))
    def key(a): return (a.u.key(), a.v.key())

def probe(m, legs, dmax=12):
    F = make_nf(m)
    class K(K2): pass
    K.F = F
    c = F.gen()                       # 2 cos(pi/m)
    half = F.const(Fr(1, 2))
    cos = c*half                      # cos(pi/m) in F
    S2 = F.const(1) - cos*cos         # sin^2 in F
    K.S2 = S2
    COS = K(cos, F.const(0))
    SIN = K(F.const(0), F.const(1))
    chk = COS*COS + SIN*SIN
    assert chk.u.key() == F.const(1).key() and chk.v.isz()
    O = K.const(0); I = K.const(1)
    def refl(p0, d):
        L = d[0]*d[0] + d[1]*d[1]
        Li = L.inv()
        m11 = (d[0]*d[0] - d[1]*d[1])*Li
        m12 = (K.const(2)*d[0]*d[1])*Li
        tx = p0[0] - (m11*p0[0] + m12*p0[1])
        ty = p0[1] - (m12*p0[0] - m11*p0[1])
        return (m11, m12, m12, -m11, tx, ty)
    a, b = legs
    V0 = (K.const(a), O); V1 = (K.const(b)*COS, K.const(b)*SIN)
    gens = [(I, O, O, -I, O, O),
            refl((O, O), (COS, SIN)),
            refl(V0, (V1[0]-V0[0], V1[1]-V0[1]))]
    idm = (I, O, O, I, O, O)
    # hard checks: field inverse and involutions
    tst = K(F.gen(), F.const(3)) + K.const(2)
    pr = tst*tst.inv()
    assert pr.u.key() == F.const(1).key() and pr.v.isz(), "field inverse broken"
    for g in gens:
        gg = (g[0]*g[0]+g[1]*g[2], g[0]*g[1]+g[1]*g[3],
              g[2]*g[0]+g[3]*g[2], g[2]*g[1]+g[3]*g[3],
              g[0]*g[4]+g[1]*g[5]+g[4], g[2]*g[4]+g[3]*g[5]+g[5])
        assert all(gg[i].key() == idm[i].key() for i in range(6)), "generator not an involution"
    def hk(g):
        return hashlib.blake2b(repr(tuple(x.key() for x in g)).encode(),
                               digest_size=16).digest()
    seen = {hk(idm)}
    front = [idm]
    seq = [1]
    t0 = time.time()
    for d in range(1, dmax+1):
        new = []
        for M in front:
            for g in gens:
                N = (g[0]*M[0]+g[1]*M[2], g[0]*M[1]+g[1]*M[3],
                     g[2]*M[0]+g[3]*M[2], g[2]*M[1]+g[3]*M[3],
                     g[0]*M[4]+g[1]*M[5]+g[4], g[2]*M[4]+g[3]*M[5]+g[5])
                k = hk(N)
                if k not in seen:
                    seen.add(k); new.append(N)
        front = new
        seq.append(len(new))
        print(f"   m={m} legs {legs} d={d:2d}: layer {len(new):5d} "
              f"[{time.time()-t0:.0f}s, rss {rss_gb():.2f}GB]", flush=True)
        assert rss_gb() < 4.0, "RSS guard"
    return seq

import sympy as sp
t = sp.symbols('t')
def abstract(m, N):
    Dm = (1+t)*sum(t**i for i in range(m)); inv = 1 - 3/(1+t) + 1/Dm
    W = sp.cancel(1/(inv.subs(t, 1/t))); ser = sp.series(W, t, 0, N+1).removeO()
    return [int(sp.expand(ser).coeff(t, k)) for k in range(N+1)]

for m in (8, 9, 10, 12):
    am = abstract(m, 12)
    print(f"m={m} abstract W_{m} spheres: {am}")
    for legs in [(1, 2), (2, 3)]:
        r = probe(m, legs)
        dev = next((d for d in range(13) if r[d] != am[d]), None)
        if dev is None:
            print(f"   => m={m} legs {legs}: NO deficit through depth 12")
        else:
            print(f"   => m={m} legs {legs}: first deficit d={dev}, "
                  f"deficits {[am[d]-r[d] for d in range(dev, 13)]}")
