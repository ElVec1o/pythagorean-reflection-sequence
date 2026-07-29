import pathlib
DATA = pathlib.Path(__file__).resolve().parents[2] / 'data' / 'triangle_relations'
# Verify the 132 depth-12 coincidences (universal132_words.json) as EXACT
# POLYNOMIAL identities in Z[p,q] -- no sympy, no rational functions, tiny memory.
# Homogeneous 3x3 matrices: A_i = L_i * [[S_i, t_i],[0,1]] has integer polynomial
# entries (L_0 = 1, L_1 = (p-1)^2+q^2, L_2 = p^2+q^2). For words w, w':
#   w == w' in G_tau for ALL nondegenerate tau
#   <=>  PA(w) * PL(w') == PA(w') * PL(w)  entrywise in Z[p,q],
# where PA = product of the A_i, PL = product of the L_i (scalar).
# Also re-verifies the 33 depth-11 pairs with the same tool.
import json, time, resource

# sparse polynomials over Z: dict {(i,j): coeff} for p^i q^j
def pmul(a, b):
    r = {}
    for (i1, j1), c1 in a.items():
        for (i2, j2), c2 in b.items():
            k = (i1+i2, j1+j2)
            v = r.get(k, 0) + c1*c2
            if v: r[k] = v
            elif k in r: del r[k]
    return r
def padd(a, b):
    r = dict(a)
    for k, c in b.items():
        v = r.get(k, 0) + c
        if v: r[k] = v
        elif k in r: del r[k]
    return r
ONE = {(0, 0): 1}
P = {(1, 0): 1}; Q = {(0, 1): 1}
def const(c): return {(0, 0): c} if c else {}
def sc(a, c): return {k: v*c for k, v in a.items()} if c else {}

# reflections for triangle (0,0),(1,0),(p,q); A = L*[[a,b,tx],[b,-a,ty],[0,0,1]]
# side 0: through (0,0),(1,0): L=1, a=1, b=0, t=0.
A0 = [[ONE, {}, {}], [{}, const(-1), {}], [{}, {}, ONE]]
L0 = ONE
# side 1: through (1,0),(p,q): d=(p-1,q); L1=(p-1)^2+q^2
dx = padd(P, const(-1)); dy = Q
L1 = padd(pmul(dx, dx), pmul(dy, dy))
a1 = padd(pmul(dx, dx), sc(pmul(dy, dy), -1))     # L*a
b1 = sc(pmul(dx, dy), 2)                          # L*b
# t = (I - S) p0, p0=(1,0):  L*tx = L - a1 ; L*ty = -b1
t1x = padd(L1, sc(a1, -1)); t1y = sc(b1, -1)
A1 = [[a1, b1, t1x], [b1, sc(a1, -1), t1y], [{}, {}, L1]]
# side 2: through (p,q),(0,0): d=(p,q); L2=p^2+q^2; p0=(0,0) so t=0
L2 = padd(pmul(P, P), pmul(Q, Q))
a2 = padd(pmul(P, P), sc(pmul(Q, Q), -1))
b2 = sc(pmul(P, Q), 2)
A2 = [[a2, b2, {}], [b2, sc(a2, -1), {}], [{}, {}, L2]]
A = [A0, A1, A2]; L = [L0, L1, L2]

def mmul(X, Y):
    return [[padd(padd(pmul(X[i][0], Y[0][j]), pmul(X[i][1], Y[1][j])),
                  pmul(X[i][2], Y[2][j])) for j in range(3)] for i in range(3)]
I3 = [[ONE, {}, {}], [{}, ONE, {}], [{}, {}, ONE]]
_c = {}
def wmat(w):
    """(PA(w), PL(w)); cache only along prefixes of the current word, cleared per pair."""
    if w in _c: return _c[w]
    if not w: return (I3, ONE)
    Mp, Lp = wmat(w[:-1])
    i = int(w[-1])
    r = (mmul(Mp, A[i]), pmul(Lp, L[i]))
    _c[w] = r
    return r

def verify(w1, w2):
    global _c
    _c = {}
    M1, l1 = wmat(w1)
    M2, l2 = wmat(w2)
    _c = {}
    for i in range(3):
        for j in range(3):
            if pmul(M1[i][j], l2) != pmul(M2[i][j], l1):
                return False
    return True

def rss_gb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**30

for name, fn, expect in [("depth-11 (33)", "universal33_words.json", 33),
                         ("depth-12 (132)", "universal132_words.json", 132)]:
    pairs = json.load(open(DATA/fn))
    t0 = time.time(); ok = 0
    for k, (w1, w2) in enumerate(pairs):
        if verify(w1, w2): ok += 1
        else: print(f"  FAIL: {w1} vs {w2}", flush=True)
        if (k+1) % 25 == 0:
            el = time.time()-t0
            print(f"  {k+1}/{len(pairs)} [{el:.0f}s, eta "
                  f"{el/(k+1)*(len(pairs)-k-1):.0f}s, rss {rss_gb():.2f}GB]", flush=True)
        assert rss_gb() < 3.0, "RSS guard tripped"
    print(f"{name}: {ok}/{len(pairs)} hold identically in Z[p,q] "
          f"[{time.time()-t0:.0f}s, rss {rss_gb():.2f}GB]")
    assert ok == len(pairs) == expect
print("\n=> every depth-12 coincidence is universal: the depth-12 sphere has "
      "6012 elements off a proper Zariski-closed set")
