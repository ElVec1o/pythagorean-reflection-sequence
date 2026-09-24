# P1a: exact Sigma (Lemma tel, N odd, eps=1) vs level-q saddle prediction near a/N = p/q + theta/(qN).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1a_saddle.py p q theta N1 N2 ... 
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, polylog, findroot, nstr, fabs
def exact_sigma(a, N):
    mp.dps = 30 + int(0.6*N/q + 30)   # enough digits for the cancellation
    z = exp(2j*pi*a/N); c = -2*(1-z); C = c**N
    w = 1/C
    for _ in range(100): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/N); u = lam**2/c
    zp = [exp(2j*pi*((a*i) % N)/N) for i in range(N)]
    tot = mpc(0); term = mpc(1); big = mpf(0)
    for r in range(N):
        t = zp[(r*r) % N]*term; tot += t; big = max(big, abs(t))
        term = term*lam*lam/((1-zp[(2*r+1) % N]*u)*(1-zp[(2*r+2) % N]*u))
    return tot, big, u
def predict(a, N, u, m):
    mp.dps = 40
    z0 = exp(2j*pi*p/q); tau = 2*pi*mpf(theta)/(q*N); U = u**q
    g = lambda f: 1j*f**2 - (1j/q**2)*(polylog(2, U*exp(2j*q*f)) - polylog(2, U)) - 2j*pi*m*f/q
    dg = lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)) - 2j*pi*m/q
    f0 = pi*m/q + 1j*mpf('0.01')
    fs = findroot(dg, f0)
    V = u*exp(2j*fs); g2 = 2j + 4j*V**q/(1-V**q)
    Cf = sqrt((1-V**q)/(1-U))
    for i in range(1, q+1): Cf *= ((1-z0**i*u)/(1-z0**i*V))**(mpf(i)/q)
    A = mpc(0)
    for rho in range(q):
        B = z0**(rho*rho)*exp(2j*rho*fs)
        for i in range(1, 2*rho+1): B /= (1-z0**i*V)
        A += B
    pref = Cf*sqrt(2*pi*tau/(-g2))/(q*tau)
    return fs, A, pref*A*exp(g(fs)/tau), g(fs)
p, q, theta = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
for N0 in [int(x) for x in sys.argv[4:]]:
    N = N0
    if q % 2 == 0 and theta % 2 == 0: print('no odd N exists for even q and even theta'); break
    while (p*N+theta) % q or N % 2 == 0 or gcd((p*N+theta)//q, N) != 1: N += 1
    a = (p*N+theta)//q
    S, big, u = exact_sigma(a, N)
    tot = 0; out = []
    for m in (range(0, 2*theta) if theta > 0 else range(0, 2*theta, -1)):
        fs, A, pr, gs = predict(a, N, u, m); tot += pr
        out.append('m%d phi*=%s g*=%s |A_q|=%s' % (m, nstr(fs, 6), nstr(gs, 6), nstr(abs(A), 6)))
    print('N', N, 'a', a, '|S|', nstr(abs(S), 8), 'maxterm', nstr(big, 4), 'S/pred', nstr(S/tot, 10), flush=True)
    for o in out: print('   ', o)
