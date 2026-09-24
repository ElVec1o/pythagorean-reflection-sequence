# P1c: RIGOROUS (Arb ball arithmetic via python-flint) certificate for the 1/12 band of P1b_band.py.
# For every M in [MLO,MHI) (M>=151), gcd(a,M)=1, 0 < 12a-M, (12a-M)^2 < M  [exact form of 0 < a/M-1/12 < 1/(12 sqrt M)],
# and NOT rigorously ell(a/M) < D := 0.05-0.000536 (borderline cases are included), it proves Sigma_M(a/M) != 0,
# hence S0 != 0 (S0_lemma Lemma 1: S0 = K*Sigma, K an exponential).
#   w  = small root of w^2-(2+X)w+1=0, X=c^M, c=-2(1-zeta): computed as 2/((2+X)+-sqrt((2+X)^2-4)), sign giving the
#        larger denominator; certified small by upper(|w|) < 1 (roots multiply to 1, so it is THE root with |w|<1).
#   lam= exp(log(1-w)/M) (principal; Re(1-w)>0), u = eps lam^2/c, Sigma by the exact recursion, all in acb balls.
# Precision: starts at PREC_BITS + M/2 bits and doubles (up to 5 times) until the ball excludes 0.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1c_band_arb.py MLO MHI [PREC_BITS]
import sys
from math import gcd
from flint import acb, arb, ctx
MLO, MHI = int(sys.argv[1]), int(sys.argv[2]); ctx.prec = int(sys.argv[3]) if len(sys.argv) > 3 else 200
def cis(k, N): return (2*arb.pi()*k/N*acb(0, 1)).exp()
def sigma(a, N):
    n0 = 1 if N % 4 == 2 else 0
    c = -2*(1 - cis(a, N)); X = c**N; B = 2 + X; s = (B*B - 4).sqrt()
    d1, d2 = B + s, B - s
    den = d1 if abs(d1).mid() >= abs(d2).mid() else d2
    w = 2/den
    if not (abs(w) < 1): raise ValueError('|w|<1 not certified')
    lam = ((1 - w).log()/N).exp(); eps = cis(-n0, N); l2e = eps*lam*lam; u = l2e/c
    zp = [cis((a*i) % N, N) for i in range(N)]
    tot = acb(0); term = acb(1); big = arb(0)
    for r in range(N):
        t = zp[(r*r) % N]*term; tot += t; at = abs(t)
        if at.upper() > big: big = at.upper()
        term = term*l2e/((1 - zp[(2*r+1) % N]*u)*(1 - zp[(2*r+2) % N]*u))
    return tot, big
Dlo = arb(0.05) - arb(0.000536)
P0 = ctx.prec; maxprec = 0
n = 0; bad = []; worst = (1e9, None); maxrad = 0
for M in range(max(MLO, 151), MHI):
    for a in range(M//12, M//12 + M//12 + 3):
        d = 12*a - M
        if gcd(a, M) != 1 or not (d > 0 and d*d < M): continue
        ell = (4*(arb.pi()*a/M).sin()).log()
        if ell < Dlo: continue                       # rigorously below D: not in the band
        ok = False; p0 = ctx.prec
        for k in range(6):                       # adaptive precision: retry at doubled precision on failure
            ctx.prec = (P0 + M//2) * 2**k
            try: tot, big = sigma(a, M)
            except ValueError as ex: why = str(ex); continue
            lo = abs(tot).lower()
            if lo > 0: ok = True; maxprec = max(maxprec, ctx.prec); break
            why = 'zero not excluded'
        ctx.prec = p0
        if not ok: bad.append((a, M, why)); continue
        n += 1
        r = float((lo/big).mid())
        if r < worst[0]: worst = (r, (a, M))
        maxrad = max(maxrad, float((abs(tot).rad()/abs(tot).mid())))
print('M in [%d,%d) prec %d: certified %d, failures %d %s, min |Sigma|_lo/max|term| = %s, max rel radius %.2e, max prec used %d'
      % (MLO, MHI, ctx.prec, n, len(bad), bad[:5], worst, maxrad, maxprec), flush=True)
