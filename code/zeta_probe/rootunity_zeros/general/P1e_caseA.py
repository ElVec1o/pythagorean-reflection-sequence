# P1e_caseA.py -- RIGOROUS (Arb) covering for Case A of Theorem M (P1e_lemma.tex):
#   for every x in [XLO, XHI] outside the excluded discs, and every N >= 151 with x = a/N,
#       sum_{m>=1, N not| m} |a_m| <= A(I) := sum_{m<60} sup_I |u0|^m/(m|1-e(-m x)|) + tau/59 < ALIM,
#   hence |Z_N - 1| <= e^{A} - 1 and |Z_N| >= 2 - e^{ALIM} > 0  (Lemma A).  The m >= 60 tail uses the hazard lemma (x in no hazard).
# Excluded discs: low seeds (radii from the P1e_lowseed certificates, given on the command line as p/q:r_left:r_right),
#   hazard discs of reduced j/n, 10 <= n <= 52 (radius 2*0.5^n/n^2), 53 <= n <= 59 (radius 0.5^n/(4 tau)).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1e_caseA.py XLO XHI ALIM p/q:rl:rr ...
import sys
from fractions import Fraction as Fr
from math import gcd
from flint import arb, acb, ctx
ctx.prec = 120
PI = arb.pi(); I = acb(0, 1)
TAU = arb('0.02'); Y = arb('0.5'); MMAX = 60
def e(z): return (2*PI*I*z).exp()
XLO, XHI, ALIM = Fr(sys.argv[1]), Fr(sys.argv[2]), arb(sys.argv[3])
disc = []   # (center Fraction, rleft, rright)
low = {}
for tok in sys.argv[4:]:
    f, rl, rr = tok.split(':'); low[Fr(f)] = (Fr(rl), Fr(rr))
for n in range(2, MMAX):
    for j in range(0, n + 1):
        if gcd(j, n) != 1: continue
        c = Fr(j, n)
        if c < XLO - Fr(1, 100) or c > XHI + Fr(1, 100): continue
        if n <= 9:
            if c in low: disc.append((c,) + low[c])
            elif XLO <= c <= XHI: print('WARNING: low rational %s has no certificate' % c)
            continue
        r = Fr(2, 2**n*n*n) if n <= 52 else Fr(25, 2**n)       # 2 y^n/n^2  or  y^n/(4 tau), y = 1/2, tau = 1/50
        disc.append((c, r, r))
disc.sort()
# complement segments of [XLO, XHI]
segs = []; cur = XLO
for c, rl, rr in disc:
    a, b = c - rl, c + rr
    if b <= cur: continue
    if a > cur: segs.append((cur, min(a, XHI)))
    cur = max(cur, b)
    if cur >= XHI: break
if cur < XHI: segs.append((cur, XHI))
print('discs %d, segments %d' % (len(disc), len(segs)), flush=True)
worst = arb(0); nev = 0; fails = []
for (a, b) in segs:
    stack = [(a, b)]
    while stack:
        lo, hi = stack.pop(); nev += 1
        xb = (arb(lo.numerator)/lo.denominator).union(arb(hi.numerator)/hi.denominator)
        # evaluate on the ball xb
        c = -2*(1 - e(xb)); cl = arb(c.abs_lower()); ell = cl.log()
        ok = bool(ell > arb('0.02'))
        if ok:
            g = (1/cl)*(1 + arb('0.1')*(-151*ell).exp()); ok = bool(g < Y)
        if ok:
            s = TAU/(MMAX - 1)
            for m in range(1, MMAX):
                den = arb((1 - e(-m*xb)).abs_lower())
                if not bool(den > 0): ok = False; break
                s += g**m/(m*den)
            ok = ok and bool(s < ALIM)
        if ok:
            worst = worst.max(s); continue
        if hi - lo < Fr(1, 10**45): fails.append((lo, hi)); continue
        mid = (lo + hi)/2; stack.append((lo, mid)); stack.append((mid, hi))
print('evaluations %d, max A <= %s, failures %d' % (nev, worst.str(4, radius=False), len(fails)))
for f in fails[:20]: print('FAIL at', float(f[0]))
if not fails: print('CASE A COVERED on [%s,%s] with A < %s' % (XLO, XHI, ALIM.str(4)))
