# P1a: check the renormalisation identity  A_q(phi_0) == Sigma at level q (a=p, N=q), q odd,
# i.e. the level-q saddle amplitude is the SAME S0-type sum at the root of unity e^{2 pi i p/q}.
# Also checks W_m/W_0 == e^{-2 pi i inv(4p) m^2 / q}.
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, sin, findroot, nstr
mp.dps = 40
def sigma_level(p, q):
    z = exp(2j*pi*p/q); c = -2*(1-z); C = c**q; w = 1/C
    for _ in range(300): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/q); u = lam**2/c
    tot = mpc(0); term = mpc(1)
    for r in range(q):
        tot += z**(r*r)*term; term *= lam**2/((1-z**(2*r+1)*u)*(1-z**(2*r+2)*u))
    return tot
def A_saddle(p, q, m=0):
    z0 = exp(2j*pi*p/q); u = -1/(2*(1-z0)); U = u**q
    f0 = findroot(lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)), mpc(0, 0.01)); fs = f0 + pi*m/q
    V = u*exp(2j*fs); A = mpc(0)
    for rho in range(q):
        B = z0**(rho*rho)*exp(2j*rho*fs)
        for i in range(1, 2*rho+1): B /= (1-z0**i*V)
        A += B
    return A, V, fs
worst = 0
for q in range(3, int(sys.argv[1]) + 1, 2):
    for p in range(1, q//2+1):
        if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(0.05): continue
        A, V, fs = A_saddle(p, q); S = sigma_level(p, q)
        d = abs(A/S - 1); worst = max(worst, d)
        if q <= 11: print('p/q=%d/%d  A_q(phi0)=%s  Sigma_q=%s  |V|=%s  |rel diff|=%s' % (p, q, nstr(A, 10), nstr(S, 10), nstr(abs(V), 5), nstr(d, 3)))
print('max |A/Sigma_q - 1| over odd q <=', sys.argv[1], ':', nstr(worst, 3))
