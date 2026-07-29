# Whole-stratum certificates for the m=4 and m=6 rows of the crystallographic
# table (analogue of the symbolic m=3 certificate).
# Setup: apex angle pi/m at the origin, legs a (along x-axis, mirror '0') and
# b (along the pi/m line, mirror '1'); mirror '2' = the far side. Coxeter
# reference W_m = <x_i | x_i^2, (x0 x1)^m>, faithful geometric representation.
# Phase 1 (exact, Q(sqrt d)): word-level enumeration at two rational leg
#   samples; classes equal in G but distinct in W_m = the early coincidences;
#   confirm (d*, delta) = (6,3) for m=4 and (8,8) for m=6, same word pairs at
#   both samples.
# Phase 2 (symbolic, Q(sqrt d)(a,b)): each extracted pair holds identically in
#   the legs => the onset holds on the WHOLE stratum; the samples witness that
#   no earlier coincidence occurs off a proper closed subset.
# Memory-careful: tiny balls (<= 768 words), RSS guard.
from fractions import Fraction as Fr
import time, resource, sys
from collections import defaultdict

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**30

class F2:  # x + y*sqrt(D)
    __slots__ = ("x", "y")
    D = 2
    def __init__(s, x=0, y=0): s.x = Fr(x); s.y = Fr(y)
    def __add__(s, o): return s.mk(s.x+o.x, s.y+o.y)
    def __sub__(s, o): return s.mk(s.x-o.x, s.y-o.y)
    def __neg__(s): return s.mk(-s.x, -s.y)
    def __mul__(s, o): return s.mk(s.x*o.x + s.D*s.y*o.y, s.x*o.y + s.y*o.x)
    def inv(s):
        d = s.x*s.x - s.D*s.y*s.y
        return s.mk(s.x/d, -s.y/d)
    def key(s): return (s.x, s.y)
    @classmethod
    def mk(c, x, y):
        r = c.__new__(c); r.x = Fr(x); r.y = Fr(y); return r

def make_field(D):
    class F(F2): pass
    F.D = D
    return F

def stratum_data(m):
    if m == 4:
        F = make_field(2)
        cos = F(0, Fr(1, 2)); sin = F(0, Fr(1, 2))       # sqrt2/2
        d_star, delta = 6, 3
    elif m == 6:
        F = make_field(3)
        cos = F(0, Fr(1, 2)); sin = F(Fr(1, 2))          # sqrt3/2, 1/2
        d_star, delta = 8, 8
    else:
        raise ValueError
    return F, cos, sin, d_star, delta

def affine_gens(F, cos, sin, a, b):
    """mirrors '0' (x-axis), '1' (theta-line), '2' (V0-V1), legs a,b rational."""
    O, I = F(0), F(1)
    def refl_line(p0, d):
        L = d[0]*d[0] + d[1]*d[1]
        Li = L.inv()
        m11 = (d[0]*d[0] - d[1]*d[1])*Li
        m12 = (F(2)*d[0]*d[1])*Li
        tx = p0[0] - (m11*p0[0] + m12*p0[1])
        ty = p0[1] - (m12*p0[0] - m11*p0[1])
        return (m11, m12, m12, -m11, tx, ty)
    V0 = (F(a), O); V1 = (F(b)*cos, F(b)*sin)
    R0 = (I, O, O, -I, O, O)
    R1 = refl_line((O, O), (cos, sin))
    R2 = refl_line(V0, (V1[0]-V0[0], V1[1]-V0[1]))
    return [R0, R1, R2]

def cox_gens(F, cos):
    """geometric representation of W_m: sigma_i(x) = x - 2B(x,ai)ai,
    B(ai,ai)=1, B(a0,a1) = -cos(pi/m), B(a0,a2)=B(a1,a2)=-1."""
    O, I = F(0), F(1)
    B = [[I, -cos, -I], [-cos, I, -I], [-I, -I, I]]
    gens = []
    for i in range(3):
        M = []
        for r in range(3):
            row = []
            for c in range(3):
                v = I if r == c else O
                if r == i: v = v - F(2)*B[i][c]
                row.append(v)
            M.append(tuple(row))
        gens.append(tuple(M))
    return gens

def amul6(g, h):
    return (g[0]*h[0]+g[1]*h[2], g[0]*h[1]+g[1]*h[3],
            g[2]*h[0]+g[3]*h[2], g[2]*h[1]+g[3]*h[3],
            g[0]*h[4]+g[1]*h[5]+g[4], g[2]*h[4]+g[3]*h[5]+g[5])
def mmul3(X, Y):
    return tuple(tuple(sum((X[i][k]*Y[k][j] for k in range(3)),
                           start=type(X[0][0])(0)) for j in range(3)) for i in range(3))
def key6(g): return tuple(x.key() for x in g)
def key3(M): return tuple(x.key() for r in M for x in r)

def extract(m, a, b, verbose=True):
    F, cos, sin, d_star, delta = stratum_data(m)
    G = affine_gens(F, cos, sin, a, b)
    W = cox_gens(F, cos)
    IG = (F(1), F(0), F(0), F(1), F(0), F(0))
    IW = tuple(tuple(F(1) if i == j else F(0) for j in range(3)) for i in range(3))
    words = [("", IG, IW)]
    front = [("", IG, IW)]
    pairs = []
    for d in range(1, d_star+1):
        new = []
        for (w, Mg, Mw) in front:
            last = int(w[-1]) if w else -1
            for i in range(3):
                if i == last: continue
                nw = w + str(i)
                new.append((nw, amul6(Mg, G[i]), mmul3(Mw, W[i])))
        front = new
        # group by G-key, split by W-key
        byg = defaultdict(dict)
        for (w, Mg, Mw) in front:
            byg[key6(Mg)].setdefault(key3(Mw), w)
        extra = [sorted(v.values()) for v in byg.values() if len(v) > 1]
        # sphere counts
        gcount = len(byg)
        wcount = len({key3(Mw) for (w, Mg, Mw) in front})
        if verbose:
            print(f"   m={m} legs ({a},{b}) d={d}: G-classes {gcount}, "
                  f"W-classes {wcount}, extra-coincidence classes {len(extra)} "
                  f"[rss {rss_gb():.2f}GB]")
        assert rss_gb() < 3.0
        if d < d_star:
            assert not extra, f"coincidence EARLIER than d*={d_star}: {extra[:3]}"
        else:
            assert len(extra) == delta and all(len(e) == 2 for e in extra), \
                f"expected {delta} pair classes at d*={d_star}, got {len(extra)}"
            pairs = sorted(tuple(e) for e in extra)
    return pairs

print("PHASE 1: exact extraction at two rational leg samples per stratum")
allpairs = {}
for m in (4, 6):
    p1 = extract(m, 1, 2)
    p2 = extract(m, 2, 3)
    assert p1 == p2, f"m={m}: pair sets differ between samples"
    allpairs[m] = p1
    print(f"   m={m}: identical {len(p1)} word pairs at both samples:")
    for w1, w2 in p1: print(f"      {w1} == {w2}")

print("\nPHASE 2: symbolic verification over Q(sqrt d)(a,b)  (whole stratum)")
import sympy as sp
for m in (4, 6):
    a, b = sp.symbols('a b', positive=True)
    if m == 4: cu = su = sp.sqrt(2)/2
    else: cu, su = sp.sqrt(3)/2, sp.Rational(1, 2)
    V0 = (a, sp.Integer(0)); V1 = (b*cu, b*su)
    def refl(p0, d):
        L = d[0]**2 + d[1]**2
        m11 = sp.cancel((d[0]**2 - d[1]**2)/L); m12 = sp.cancel(2*d[0]*d[1]/L)
        tx = sp.expand(p0[0] - (m11*p0[0] + m12*p0[1]))
        ty = sp.expand(p0[1] - (m12*p0[0] - m11*p0[1]))
        return (m11, m12, m12, -m11, tx, ty)
    SG = {'0': (sp.Integer(1), sp.Integer(0), sp.Integer(0), sp.Integer(-1),
                sp.Integer(0), sp.Integer(0)),
          '1': refl((sp.Integer(0), sp.Integer(0)), (cu, su)),
          '2': refl(V0, (V1[0]-V0[0], V1[1]-V0[1]))}
    def comp(g, h):
        return tuple(sp.expand(x) for x in (
            g[0]*h[0]+g[1]*h[2], g[0]*h[1]+g[1]*h[3],
            g[2]*h[0]+g[3]*h[2], g[2]*h[1]+g[3]*h[3],
            g[0]*h[4]+g[1]*h[5]+g[4], g[2]*h[4]+g[3]*h[5]+g[5]))
    def word(w):
        M = (sp.Integer(1), sp.Integer(0), sp.Integer(0), sp.Integer(1),
             sp.Integer(0), sp.Integer(0))
        for ch in w: M = comp(M, SG[ch])
        return M
    t0 = time.time(); ok = 0
    for w1, w2 in allpairs[m]:
        M1, M2 = word(w1), word(w2)
        good = all(sp.simplify(sp.radsimp(x - y)) == 0 for x, y in zip(M1, M2))
        ok += good
        if not good: print(f"   m={m} FAIL: {w1} vs {w2}")
        assert rss_gb() < 3.0
    print(f"   m={m}: {ok}/{len(allpairs[m])} pairs hold identically in (a,b) "
          f"[{time.time()-t0:.0f}s, rss {rss_gb():.2f}GB]")
    assert ok == len(allpairs[m])
print("\n=> the (d*,delta) rows (6,3) for m=4 and (8,8) for m=6 hold on the "
      "whole stratum: onset by the identities, exactness off a proper closed "
      "subset by the samples")
