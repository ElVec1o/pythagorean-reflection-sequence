# S_e(-q_m), D_U(-q_m) and D_V(-q_m) at high precision (heavy cancellation: the terms reach 10^{2 log10 g(-q_m)}).
# g(-p) >= 1 is proved (all terms positive); this checks the other two pole sources of U at x = +-i x_m.
# Floating point (mpmath), NOT an interval certificate.  Usage: python3 rootunity_minus.py m0 m1
import sys
from mpmath import mp, mpf, sqrt, log, nstr, findroot
src = open('/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/nondfinite/rootunity_check.py').read()
exec(src.split('guesses =')[0].replace('mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 110', ''))
guesses = [mpf('0.4494536306')] + [mpf(l.strip()) for l in open(POLES).readlines()]
m0, m1 = int(sys.argv[1]), int(sys.argv[2])
for m in range(m0, m1 + 1):
    mp.dps = 200
    g0 = guesses[m - 1]
    f = lambda t: blocks(t, Jof(t))[0]
    q = findroot(f, (g0*(1 - mpf(10)**-9), g0*(1 + mpf(10)**-12)), solver='anderson',
                 tol=mpf(10)**(-mp.dps + 15))
    gneg = blocks(-q, Jof(q))[0]
    res = []
    for extra in (60, 120):              # two precisions, both above the cancellation depth
        mp.dps = 2*int(log(gneg, 10)) + extra
        qq = -mpf(q)
        g, Se, Y, big = blocks(qq, Jof(qq))
        DU = (1 - qq**2)*(1 - qq**3)*Se - 2*qq**4*Y
        DV = (1 - qq)*(1 - qq**3)*Se - 2*qq**4*Y
        res.append((mp.dps, g, Se, DU, big, DV))
    (d1, g1, S1, D1, b1, V1), (d2, g2, S2, D2, b2, V2) = res
    mp.dps = 30
    print(m, 'g(-q)=%s' % nstr(g2, 6), 'Se(-q)=%s' % nstr(S2, 8), 'DU(-q)=%s' % nstr(D2, 8), 'DV(-q)=%s' % nstr(V2, 8), 'relchange(DV)=%s' % nstr(abs(V1/V2 - 1), 3),
          'Se*g=%s' % nstr(S2*g2, 8), 'relchange(Se)=%s' % nstr(abs(S1/S2 - 1), 3),
          'relchange(DU)=%s' % nstr(abs(D1/D2 - 1), 3), 'dps=%d,%d big=1e%d' % (d1, d2, int(log(b2, 10))),
          flush=True)
