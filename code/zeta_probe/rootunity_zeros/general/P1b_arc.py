# P1b item (5): finite check that the terminal step of the continued-fraction chain lands on the certified arc.
# Chain: level M, Dirichlet with Q = sqrt(M): |a/M - p/q| < 1/(q sqrt M), q <= sqrt M; stop at first q <= QC.
# Non-terminal steps drift ell by <= 12.2 * sum 1/M_{j+1}^2 <= DRIFT (PROVED in report_P1b.md, sec. 5).
# Terminal step: need every p/q (q<=QC) with ell(p/q) < DC to be at distance >= 1/(q sqrt(QC+1)) from {ell >= D - DRIFT}.
# Exact-enough: uses mpmath at 30 digits on explicit arcsin. Usage: python3 P1b_arc.py D DC [QC]
import sys
from math import gcd
from mpmath import mp, mpf, asin, exp, pi, sin, log, sqrt
mp.dps = 30
D, DC = mpf(sys.argv[1]), mpf(sys.argv[2]); QC = int(sys.argv[3]) if len(sys.argv) > 3 else 150
DRIFT = mpf('12.2')*sum(mpf(1)/mpf(QC+1)**(2**k) for k in range(1, 8))
xe = asin(exp(D - DRIFT)/4)/pi          # arc {ell >= D-DRIFT} ∩ [0,1/2] = [xe, 1/2]
bad = []
for q in range(1, QC+1):
    for p in range(0, q//2+1):
        if gcd(p, q) != 1: continue
        x = mpf(p)/q
        ell = log(4*sin(pi*x)) if p else mpf('-inf')
        if ell >= DC: continue
        if xe - x < 1/(q*sqrt(QC+1)): bad.append((p, q, float(ell), float(xe-x), float(1/(q*sqrt(QC+1)))))
print('D', D, 'DC', DC, 'QC', QC, 'drift bound', float(DRIFT), 'violations', len(bad))
for b in bad[:20]: print('  p/q=%d/%d ell=%.4f dist=%.5f needed=%.5f' % b)
