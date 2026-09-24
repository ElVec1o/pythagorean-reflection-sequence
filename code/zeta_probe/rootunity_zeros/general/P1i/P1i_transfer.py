# P1i_transfer.py -- Arb certificate of the P1f Theorem C transfer conditions (Z_N, Z^+_N nonzero and the six
# omega-conditions, both roots) for every reduced a/N, a/N != 1/2, in [XLO, 1-XLO] with N1 <= N <= N2.
# Reuses check() of ../P1f/P1f_transfer_cert.py verbatim (exact finite formula + rigorous tail).  FAILS LOUDLY.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1i_transfer.py N1 N2 [XLO=0.143]
import sys, os
from math import gcd
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '..')); sys.path.insert(0, os.path.join(here, '..', 'P1f'))
os.chdir(os.path.join(here, '..', 'P1f'))
from P1f_transfer_cert import check
from dround import fdn
N1, N2 = int(sys.argv[1]), int(sys.argv[2]); xlo = float(sys.argv[3]) if len(sys.argv) > 3 else 0.143
cnt = 0; mn = None
for N in range(N1, N2 + 1):
    for a in range(1, N):
        if gcd(a, N) != 1 or not (xlo <= a/N <= 1 - xlo) or 2*a == N: continue
        m, om = check(a, N)
        if m is None: print('CERT FAILED at %d/%d' % (a, N), flush=True); sys.exit(1)
        print('%d/%d  min certified modulus of Z, Z+, six factors >= %s   omega ~ %s' % (a, N, fdn(m), om.str(6, radius=False)), flush=True)
        cnt += 1; mn = m if mn is None else mn.min(m)
print('TRANSFER CERT PASSED: %d cases, %d<=N<=%d, [%.3f, %.3f], min modulus >= %s' % (cnt, N1, N2, xlo, 1 - xlo, fdn(mn)), flush=True)
