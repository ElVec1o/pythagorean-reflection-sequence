# P1h_caseA.py -- RIGOROUS (Arb) refined direct covering on the NEW region R0 = [1/6, 1/5] (hazard base y0 = 0.52).
# For every x in [XLO, XHI] outside the excluded discs, and every N >= 151 with x = a/N, gcd(a,N)=1, and s in {0,+1,-1}:
#     Z^s_N = P^s_M(x) + R,   P^s_M(x) = sum_{n<=M} psi'_n(x) e(-(n^2 + s n) x),
# where psi'_n are the coefficients of exp(sum_{m<60} a_m Y^m)  (a_m = u0^m/(m(1-e(-m x))), exact; N does not divide m<60),
#     |R| <= T := e^{A}(e^{tau/59} - 1) + (e^{A} - sum_{n<=M} c_n),   A = sum_{m<60} alpha_m,  alpha_m >= sup |a_m|,
# c_n = coefficients of exp(sum_{m<60} alpha_m Y^m).  Proof of the bound: e^{Phi} = e^{Phi_<60} e^{Phi_>=60}, the second factor
# has coefficient sum <= e^{tau/59} (P1e Lemma H(3) with y0: sum_{m>=60}|a_m| <= tau/59), so
#     sum_n |psi_n - psi'_n| <= e^{A}(e^{tau/59}-1),   sum_{n>M} |psi'_n| <= e^{A} - sum_{n<=M} c_n.
# (For M <= 59 this is P1g's bound; M may now exceed 59 -- needed near the seed 1/6.)
# Certifies on each interval |Z^s| >= ZREQ (s=0,+1,-1) and every normalised transfer factor |G_i| >= MREQ (P1g Def. G).
# u0 in (1/c)(1 + D(0.1 e^{-151 l})) (P1d Lemma W).  FAILS LOUDLY (exit 1).
# Excluded discs: low seeds (p/q:rl:rr), hazards of reduced j/n, 10<=n<=59: radius 2 y0^n/n^2 (n<=52), y0^n/(4 tau) (n>=53).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1h_caseA.py XLO XHI ZREQ MREQ p/q:rl:rr ...
import sys
from fractions import Fraction as Fr
from math import gcd
from flint import arb, acb, ctx
sys.path.insert(0, '..'); sys.path.insert(0, '../P1g')
from dround import fdn, fup
from P1g_seeds import Gfactors
ctx.prec = 100
PI = arb.pi(); I = acb(0, 1)
import os
YS = os.environ.get('P1H_Y', '0.52')      # region hazard base (R0: 0.52, R1: 0.59)
ZONLY = bool(os.environ.get('P1H_ZONLY'))   # certify only |Z^0| (Theorem M'), skip Z^pm and the omega margins
TAU = arb('0.02'); Y = arb(YS); YF = Fr(YS); MMAX = 60
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
            r = 2*YF**n/(n*n) if n <= 52 else YF**n*Fr(25, 2)      # y0^n/(4 tau) = 12.5 y0^n
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
    a = [acb(0)]*MMAX; al = [arb(0)]*MMAX; um = acb(1); A = arb(0)
    for m in range(1, MMAX):
        um = um*u
        den = 1 - e(-m*xb)
        if not bool(arb(den.abs_lower()) > 0): return None, 'den'
        a[m] = um/(m*den); al[m] = arb(a[m].abs_upper()); A += al[m]
    ps = [acb(1)] + [acb(0)]*M; cs = [arb(1)] + [arb(0)]*M
    for k in range(1, M + 1):
        s1 = acb(0); s2 = arb(0)
        for j in range(1, min(k, MMAX - 1) + 1):
            s1 += j*a[j]*ps[k - j]; s2 += j*al[j]*cs[k - j]
        ps[k] = s1/k; cs[k] = s2/k
    eA = A.exp()
    T = arb((eA*(TAU/(MMAX - 1)).expm1() + (eA - sum(cs, arb(0)))).upper())
    if not bool(T >= 0): return None, 'T'
    tb = acb(arb(0, T.upper()), arb(0, T.upper()))
    Zs = {}
    for s in (0, 1, -1):
        Zs[s] = sum((ps[n]*e(-(n*n + s*n)*xb) for n in range(M + 1)), acb(0)) + tb
    zl = arb(Zs[0].abs_lower()).min(arb(Zs[1].abs_lower())).min(arb(Zs[-1].abs_lower()))
    if ZONLY:
        z0 = arb(Zs[0].abs_lower())
        if not bool(z0 > ZREQ): return None, 'Z T=%s' % T.str(3, radius=False)
        return (z0, arb(1), arb(0), A, T, z0), 'ok'
    if not bool(zl > ZREQ): return None, 'Z T=%s' % T.str(3, radius=False)
    om = Zs[-1]/(u*Zs[1]); t1 = -(1 + om)/2
    G = Gfactors(z, t1, e(xb/2))
    mg = arb(G[0].abs_lower())
    for gg in G[1:]: mg = mg.min(arb(gg.abs_lower()))
    if not bool(mg > MREQ): return None, 'margin T=%s' % T.str(3, radius=False)
    return (zl, mg, arb(om.abs_upper()), A, T, arb(Zs[0].abs_lower())), "ok"
if __name__ == '__main__':
    XLO, XHI, ZREQ, MREQ = Fr(sys.argv[1]), Fr(sys.argv[2]), arb(sys.argv[3]), arb(sys.argv[4])
    low = {}
    for tok in sys.argv[5:]:
        f, rl, rr = tok.split(':'); low[Fr(f)] = (Fr(rl), Fr(rr))
    segs = build_discs(XLO, XHI, low)
    print('segments %d' % len(segs), flush=True)
    worstZ = None; worstZ0 = None; worstM = None; maxom = arb(0); maxT = arb(0); nev = 0; nok = 0; Mhist = {}
    for (a0, b0) in segs:
        stack = [(a0, b0)]
        while stack:
            lo, hi = stack.pop(); nev += 1
            res = None
            for M in (8, 20, 40, 59, 100, 160, 260, 400):
                res, why = evaluate(lo, hi, M, ZREQ, MREQ)
                if res is not None or not why.startswith(('Z', 'margin')): break
                T = float(why.split('T=')[1].split()[0].strip('[]')) if 'T=' in why else 1
                if T < 1e-3: break
            if res is not None:
                zl, mg, oa, A, T, z0 = res; nok += 1; Mhist[M] = Mhist.get(M, 0) + 1
                worstZ = zl if worstZ is None else worstZ.min(zl)
                worstZ0 = z0 if worstZ0 is None else worstZ0.min(z0)
                if worstM is None or bool(mg < worstM): worstM = mg; wloc = (float(lo), float(hi))
                maxom = maxom.max(oa); maxT = maxT.max(T)
                continue
            if hi - lo < Fr(1, 10**30):
                print('CASEA FAILED at x in [%.17g, %.17g] (%s)' % (float(lo), float(hi), why), flush=True); sys.exit(1)
            mid = (lo + hi)/2; stack.append((mid, hi)); stack.append((lo, mid))
    print('CASEA PASSED on [%s,%s]: %d intervals (%d evaluations), M-histogram %s, min|Z|>=%s, min|Z^s|(s=0,+-1)>=%s, min margin>=%s (at x in [%.9g,%.9g]), max|omega|<=%s, max T<=%s' % (
        XLO, XHI, nok, nev, sorted(Mhist.items()), fdn(worstZ0), fdn(worstZ), fdn(worstM), wloc[0], wloc[1], fup(maxom), fup(maxT)), flush=True)
