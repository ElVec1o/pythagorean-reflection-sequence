# P1g_margin_profile.py -- VERIFIED (point evaluations, not a covering): the N -> infinity profile of the omega-margin
# min_i |G_i| of the refined direct formula (P1g_caseA.evaluate at degenerate balls x = k/K), over x in [1/5, 1/2],
# skipping points that fail (inside discs / hazards).  Prints the 12 smallest margins found.
import sys
from fractions import Fraction as Fr
from flint import arb
import P1g_caseA as CA
K = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
res = []
for k in range(K//5, K//2):
    x = Fr(k, K)
    r, why = CA.evaluate(x, x, 40, arb(-1), arb(-1))
    if r is None or float(r[4].mid()) > 2e-3: continue   # keep only points where the tail T_M <= 2e-3 (sharp enclosure)
    res.append((float(r[1].mid()), float(x), float(r[2].mid())))
res.sort()
for m in res[:12]: print('margin %.4f at x=%.6f |omega|~%.3f' % m)
print('points evaluated: %d' % len(res))
