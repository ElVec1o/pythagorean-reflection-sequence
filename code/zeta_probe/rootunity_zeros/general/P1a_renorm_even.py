# P1a: even q. Surviving saddle amplitude vs the level-q Sigma with the twist of S0_lemma (n0=1 iff q=2 mod 4).
import sys
from math import gcd
exec(open(__file__.replace('P1a_renorm_even.py', 'P1a_renorm.py')).read().split('worst = 0')[0])
def sigma_level_tw(p, q):
    n0 = (-1 if TW < 0 else 1) if q % 4 == 2 else 0
    z = exp(2j*pi*p/q); c = -2*(1-z); C = c**q; w = 1/C
    for _ in range(300): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/q); eps = exp(-2j*pi*n0/q); u = eps*lam**2/c
    tot = mpc(0); term = mpc(1)
    for r in range(q):
        tot += z**(r*r)*term; term *= eps*lam**2/((1-z**(2*r+1)*u)*(1-z**(2*r+2)*u))
    return tot
TW = int(sys.argv[2]) if len(sys.argv) > 2 else 1
for q in range(2, int(sys.argv[1])+1, 2):
    for p in range(1, q//2+1):
        if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(0.05): continue
        S = sigma_level_tw(p, q)
        As = [A_saddle(p, q, m)[0] for m in (0, 1)]
        print('p/q=%d/%d  A(phi_0)=%s A(phi_1)=%s  Sigma_q(twist n0=%d)=%s' % (p, q, nstr(As[0], 10), nstr(As[1], 10), TW, nstr(S, 10)))
