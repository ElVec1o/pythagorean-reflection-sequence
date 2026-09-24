# P1b item (5): the only terminal obstruction for delta=0.05 is the degenerate level-12 point 1/12 (|w_12|=1).
# Chains can reach it only from a/M with 151<=M<3600, ell(a/M)>=0.05-DRIFT and 0 < a/M-1/12 < 1/(12 sqrt M).
# This script evaluates Sigma_M at every such a/M in floating point (two precisions) -- VERIFIED(float), not interval.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1b_band.py MLO MHI
import sys
from math import gcd, sqrt as fsqrt
from mpmath import mp, mpf, exp, pi, log, sin, nstr
from P1b_scan import sigma
MLO, MHI = int(sys.argv[1]), int(sys.argv[2])
D = 0.05 - 0.000536
n = 0; worst = (1e9, None); maxdiff = 0
for M in range(max(MLO, 151), MHI):
    for a in range(M//12, M//12 + M//(12*int(fsqrt(M))) + 3):
        if gcd(a, M) != 1: continue
        x = a/M
        if not (0 < x - 1/12 < 1/(12*fsqrt(M))): continue
        mp.dps = 30
        if log(4*sin(pi*mpf(a)/M)) < D: continue
        S1, big = sigma(a, M); mp.dps = 45; S2, _ = sigma(a, M)
        maxdiff = max(maxdiff, abs(S1/S2 - 1)); n += 1
        r = abs(S2)/big
        if r < worst[0]: worst = (float(r), (a, M), float(abs(S2)/fsqrt(M)))
print('M in [%d,%d): cases %d, precision discrepancy %s, min |Sigma|/max|term| = %s' % (MLO, MHI, n, nstr(maxdiff, 3), worst), flush=True)
