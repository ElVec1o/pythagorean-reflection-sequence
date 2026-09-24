# P1h_hazard_check.py -- RIGOROUS (Arb): the numerical facts used in the proof of P1e Lemma H (hazard combinatorics),
# re-checked for a region hazard base y (P1h uses y = 0.52 on R0 = [1/6,1/5], y = 0.59 on R1 = [0.143,1/6]); tau = 1/50.
# Hazard radii: eps_n = 2 y^n/n^2 (10<=n<=52), y^n/(4 tau) (n>=53).  Checks (numbering as in P1h_lemma.tex, Lemma H_y):
#  (H1) n^2 eps_n <= 1/2 for all n >= 10                      [(1), and the shallower-hazard subcase n m' eps_n <= 1/2]
#  (H2) y^{max(60,2m')}/(4 tau) <= 2 y^{m'}/m'^2, 10<=m'<=52   [middle case]
#  (H3) eps_n < log(1/y)/(2n)  and  f(eps_n) = eps_n y^{-1/(2 n eps_n)} >= 1/(4 tau)   [the m'=n, i'=j subcase]
#       for n >= 53 this is  y^{-n} >= 25 n^2 (checked up to n=10^4; beyond, y^{-1} >= (1+1/n)^2 makes it monotone)
#  (H4) y^{n2min+1}/(4 tau) < 1/(2 n^2) with n2min = floor(1/(2 n eps_n)) - 1   [shallower subcase, replaces 'n2 >= 2560']
#  (H5) y^60/(4 tau) < 1e-6 (below every low-seed radius used) and 12.5 y^m < 1/(9m) for m >= 60 (no crossing of a
#       low-height region boundary p/q, q <= 9; monotone in m)
# FAILS LOUDLY.  Usage: python3 P1h_hazard_check.py y
import sys
from flint import arb
y = arb(sys.argv[1]); tau = arb('0.02'); ly = (1/y).log()
def eps(n): return 2*y**n/n**2 if n <= 52 else y**n/(4*tau)
bad = []
for n in range(10, 10001):
    e = eps(n)
    if not bool(n*n*e <= arb(1)/2): bad.append(('H1', n))
    if not bool(e < ly/(2*n)): bad.append(('H3a', n))
    lf = e.log() + ly/(2*n*e)          # log f(eps_n)
    if not bool(lf >= (1/(4*tau)).log()): bad.append(('H3b', n))
    v = float((1/(2*n*e)).lower())
    n2 = min(int(v) - 1, 10**6) if v < 1e7 else 10**6   # a lower bound for n2 (larger n2 only helps)
    if not bool(y**(n2 + 1)/(4*tau) < 1/(2*n*n)): bad.append(('H4', n))
for m in range(10, 53):
    if not bool(y**max(60, 2*m)/(4*tau) <= 2*y**m/m**2): bad.append(('H2', m))
if not bool(y**60/(4*tau) < arb('1e-6')): bad.append(('H5a', 60))
if not bool(12.5*y**60 < arb(1)/(9*60)): bad.append(('H5b', 60))
if not bool(1/y >= (1 + arb(1)/53)**2): bad.append(('mono', 53))
if bad: print('HAZARD CHECK FAILED y=%s: %s' % (sys.argv[1], bad[:10])); sys.exit(1)
print('HAZARD CHECK PASSED y=%s: H1-H5 for 10<=n<=10000 (monotone beyond)' % sys.argv[1])
