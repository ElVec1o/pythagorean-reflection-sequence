# P1g_caseA.py -- RIGOROUS (Arb) refined direct covering (P1g Lemma A^pm): for every x in [XLO, XHI] outside the excluded discs
# and every N >= 151 with x = a/N, gcd(a,N) = 1:
#     Z^s_N = P^s_M(x) + R,  |R| <= T_M(x),   s in {+1,-1},
#     P^s_M(x) = sum_{n<=M} psi_n(x) e(-(n^2 + s n) x)   (psi_n: e^{Phi} = sum psi_n Y^n, exact for n <= M < 60 <= 151 <= N),
#     T_M = exp(A) - sum_{n<=M} c_n,  A = sum_{m<60} alpha_m + tau/59,  c_n = coefficients of exp(sum_{m<60} alpha_m Y^m),
#     alpha_m >= sup_I |a_m|,  a_m = u0^m/(m(1 - e(-m x))),  u0 in (1/c)(1 + D(0.1 e^{-151 l}))  (Lemma W).
# The m >= 60 tail (<= tau/59) is Lemma H(3) of P1e (x in no hazard of height >= 10 and in no low-seed disc).
# On each interval it certifies |Z^s| >= ZREQ and every normalised transfer factor |G_i| >= MREQ (P1g Def. G), with
# omega = Z^-/(u0 Z^+).  FAILS LOUDLY (exit 1) on any interval that cannot be certified down to width 1e-30.
# Excluded discs: low seeds p/q (radii given as p/q:rl:rr), hazards of reduced j/n, 10<=n<=59 (radius 2y^n/n^2 resp. y^n/(4tau)).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1g_caseA.py XLO XHI ZREQ MREQ p/q:rl:rr ...
import sys
from fractions import Fraction as Fr
from math import gcd
from flint import arb, acb, ctx
sys.path.insert(0, '..')
from dround import fdn, fup
from P1g_seeds import Gfactors
ctx.prec = 100
PI = arb.pi(); I = acb(0, 1)
TAU = arb('0.02'); Y = arb('0.5'); MMAX = 60
def e(z): return (2*PI*I*z).exp()
def build_discs(XLO, XHI, low):
    disc = []
    for n in range(2, MMAX):
        for j in range(0, n + 1):
            if gcd(j, n) != 1: continue
            c = Fr(j, n)
            if c < XLO - Fr(1, 100) or c > XHI + Fr(1, 100): continue
            if n <= 9:
                if c in low: disc.append((c,) + low[c])
                elif XLO <= c <= XHI: raise SystemExit('CASEA FAILED: low rational %s has no disc' % c)
                continue
            r = Fr(2, 2**n*n*n) if n <= 52 else Fr(25, 2**n)
            disc.append((c, r, r))
    disc.sort()
    segs = []; cur = XLO
    for c, rl, rr in disc:
        a, b = c - rl, c + rr
        if b <= cur: continue
        if a > cur: segs.append((cur, min(a, XHI)))
        cur = max(cur, b)
        if cur >= XHI: break
    if cur < XHI: segs.append((cur, XHI))
    return segs
def evaluate(lo, hi, M, ZREQ, MREQ):
    xb = (arb(lo.numerator)/lo.denominator).union(arb(hi.numerator)/hi.denominator)
    z = e(xb); c = -2*(1 - z); cl = arb(c.abs_lower()); ell = cl.log()
    if not bool(ell > arb('0.02')): return None, 'ell'
    el = arb((arb('0.1')*(-151*ell).exp()).upper())
    u = (1/c)*(1 + acb(arb(0, el), arb(0, el)))
    g = arb(u.abs_upper())
    if not bool(g < Y): return None, 'g'
    a = [acb(0)]*MMAX; al = [arb(0)]*MMAX; um = acb(1); A = TAU/(MMAX - 1)
    for m in range(1, MMAX):
        um = um*u
        den = 1 - e(-m*xb)
        if not bool(arb(den.abs_lower()) > 0): return None, 'den'
        a[m] = um/(m*den); al[m] = arb(a[m].abs_upper()); A += al[m]
    # exact psi_n and majorant c_n, n <= M
    ps = [acb(1)] + [acb(0)]*M; cs = [arb(1)] + [arb(0)]*M
    for k in range(1, M + 1):
        s1 = acb(0); s2 = arb(0)
        for j in range(1, k + 1):
            s1 += j*a[j]*ps[k - j]; s2 += j*al[j]*cs[k - j]
        ps[k] = s1/k; cs[k] = s2/k
    T = arb((A.exp() - sum(cs, arb(0))).upper())
    if not bool(T >= 0): return None, 'T'
    tb = acb(arb(0, T.upper()), arb(0, T.upper()))
    Zs = {}
    for s in (1, -1):
        Zs[s] = sum((ps[n]*e(-(n*n + s*n)*xb) for n in range(M + 1)), acb(0)) + tb
    zl = arb(Zs[1].abs_lower()).min(arb(Zs[-1].abs_lower()))
    if not bool(zl > ZREQ): return None, 'Z T=%s' % T.str(3, radius=False)
    om = Zs[-1]/(u*Zs[1]); t1 = -(1 + om)/2
    G = Gfactors(z, t1, e(xb/2))
    mg = arb(G[0].abs_lower())
    for gg in G[1:]: mg = mg.min(arb(gg.abs_lower()))
    if not bool(mg > MREQ): return None, 'margin T=%s' % T.str(3, radius=False)
    return (zl, mg, arb(om.abs_upper()), A, T), "ok"
if __name__ == '__main__':
    XLO, XHI, ZREQ, MREQ = Fr(sys.argv[1]), Fr(sys.argv[2]), arb(sys.argv[3]), arb(sys.argv[4])
    low = {}
    for tok in sys.argv[5:]:
        f, rl, rr = tok.split(':'); low[Fr(f)] = (Fr(rl), Fr(rr))
    segs = build_discs(XLO, XHI, low)
    print('segments %d' % len(segs), flush=True)
    worstZ = None; worstM = None; maxom = arb(0); maxA = arb(0); nev = 0; nok = 0; Mhist = {}
    for (a0, b0) in segs:
        stack = [(a0, b0)]
        while stack:
            lo, hi = stack.pop(); nev += 1
            res = None
            for M in (8, 20, 40, 59):
                res, why = evaluate(lo, hi, M, ZREQ, MREQ)
                if res is not None or not why.startswith(('Z', 'margin')): break
                if why.startswith(('Z', 'margin')):
                    T = float(why.split('T=')[1].split()[0].strip('[]')) if 'T=' in why else 1
                    if T < 1e-3: break          # tail already small: failure is ball width -> bisect
            if res is not None:
                zl, mg, oa, A, _T = res; nok += 1; Mhist[M] = Mhist.get(M, 0) + 1
                worstZ = zl if worstZ is None else worstZ.min(zl); 
                if worstM is None or bool(mg < worstM): worstM = mg; wloc = (float(lo), float(hi))
                maxom = maxom.max(oa); maxA = maxA.max(A)
                continue
            if hi - lo < Fr(1, 10**30):
                print('CASEA FAILED at x in [%.17g, %.17g] (%s)' % (float(lo), float(hi), why), flush=True); sys.exit(1)
            mid = (lo + hi)/2; stack.append((mid, hi)); stack.append((lo, mid))
        # progress
    print('CASEA PASSED on [%s,%s]: %d intervals certified (%d evaluations), M-histogram %s, min|Z^pm|>=%s, min margin>=%s (at x in [%.9g,%.9g]), max|omega|<=%s, max A<=%s' % (
        XLO, XHI, nok, nev, sorted(Mhist.items()), fdn(worstZ), fdn(worstM), wloc[0], wloc[1], fup(maxom), fup(maxA)), flush=True)
