# P1c: empirical error constant c(p/q,theta) = |Sigma_N/Main - 1| * N/|theta| of the P1a multi-saddle asymptotic,
# N odd (eps=1). Tests whether c is bounded uniformly in q (needed for the Dirichlet chain q,|theta|<=sqrt N).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1c_errconst.py N theta q1 q2 ...   (all p on arc ell>=0.05, p<=q/2)
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, polylog, findroot, nstr, sin
def exact_sigma(a, N, q):
    mp.dps = 30 + int(0.6*N/q + 30)
    z = exp(2j*pi*a/N); c = -2*(1-z); C = c**N; w = 1/C
    for _ in range(200): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/N); u = lam**2/c
    zp = [exp(2j*pi*((a*i) % N)/N) for i in range(N)]
    tot = mpc(0); term = mpc(1)
    for r in range(N):
        tot += zp[(r*r) % N]*term
        term = term*lam*lam/((1-zp[(2*r+1) % N]*u)*(1-zp[(2*r+2) % N]*u))
    return tot, u
def predict(p, q, theta, N, u, m):
    z0 = exp(2j*pi*p/q); tau = 2*pi*mpf(theta)/(q*N); U = u**q
    g = lambda f: 1j*f**2 - (1j/q**2)*(polylog(2, U*exp(2j*q*f)) - polylog(2, U)) - 2j*pi*m*f/q
    dg = lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)) - 2j*pi*m/q
    fs = findroot(dg, pi*m/q + 1j*mpf('0.01'))
    V = u*exp(2j*fs); g2 = 2j + 4j*V**q/(1-V**q)
    Cf = sqrt((1-V**q)/(1-U))
    for i in range(1, q+1): Cf *= ((1-z0**i*u)/(1-z0**i*V))**(mpf(i)/q)
    A = mpc(0); T = mpc(1)
    for rho in range(q):
        A += z0**(rho*rho)*exp(2j*rho*fs)*T
        T /= (1-z0**(2*rho+1)*V)*(1-z0**(2*rho+2)*V)
    return Cf*sqrt(2*pi*tau/(-g2))/(q*tau)*A*exp(g(fs)/tau)
import os
N0, theta = int(sys.argv[1]), int(sys.argv[2])
PLIST = [int(x) for x in os.environ.get('PLIST','').split(',') if x]  # optional: restrict p
for q in [int(x) for x in sys.argv[3:]]:
    for p in (PLIST if PLIST else range(1, q//2+1)):
        if gcd(p, q) != 1 or 4*sin(pi*mpf(p)/q) < exp(mpf('0.05')): continue
        if q % 2 == 0 and theta % 2 == 0: continue
        N = N0
        while (p*N+theta) % q or N % 2 == 0 or gcd((p*N+theta)//q, N) != 1: N += 1
        a = (p*N+theta)//q
        S, u = exact_sigma(a, N, q); mp.dps = 40
        ms = range(0, 2*theta) if theta > 0 else range(0, 2*theta, -1)
        P = sum(predict(p, q, theta, N, u, m) for m in ms)
        r = S/P
        e = min(abs(r-1), abs(r+1))
        print('p/q=%d/%d N=%d ratio=%s  c=|r-+1|*N/|theta|=%s' % (p, q, N, nstr(r, 8), nstr(e*N/abs(theta), 5)), flush=True)
