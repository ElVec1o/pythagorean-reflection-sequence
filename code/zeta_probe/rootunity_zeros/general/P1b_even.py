# P1b item (4): N even. Exact Sigma_N (twist eps=e^{-2 pi i n0/N}, n0=1 iff N=2 mod 4, as in S0_lemma)
# vs the P1a multi-saddle prediction, evaluated with the ACTUAL level-N u (which contains eps).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1b_even.py p q theta N1 N2 ...   (N_i rounded up to admissible)
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, polylog, findroot, nstr
def exact_sigma(a, N, q):
    mp.dps = 30 + int(0.6*N/q + 30)
    n0 = 1 if N % 4 == 2 else 0
    z = exp(2j*pi*a/N); c = -2*(1-z); C = c**N; w = 1/C
    for _ in range(100): w = (1-w)**2/C
    lam = (1-w)**(mpf(1)/N); eps = exp(-2j*pi*n0/N); u = eps*lam*lam/c
    zp = [exp(2j*pi*((a*i) % N)/N) for i in range(N)]
    tot = mpc(0); term = mpc(1)
    for r in range(N):
        tot += zp[(r*r) % N]*term
        term = term*eps*lam*lam/((1-zp[(2*r+1) % N]*u)*(1-zp[(2*r+2) % N]*u))
    return tot, u, eps
def predict(p, q, theta, N, u, m, eps):
    mp.dps = 40
    z0 = exp(2j*pi*p/q); tau = 2*pi*mpf(theta)/(q*N); U = u**q
    g = lambda f: 1j*f**2 - (1j/q**2)*(polylog(2, U*exp(2j*q*f)) - polylog(2, U)) - 2j*pi*m*f/q
    dg = lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)) - 2j*pi*m/q
    fs = findroot(dg, pi*m/q + 1j*mpf('0.01'))
    V = u*exp(2j*fs); g2 = 2j + 4j*V**q/(1-V**q)
    Cf = sqrt((1-V**q)/(1-U))
    for i in range(1, q+1): Cf *= ((1-z0**i*u)/(1-z0**i*V))**(mpf(i)/q)
    A = mpc(0)
    for rho in range(q):
        B = z0**(rho*rho)*exp(2j*rho*fs)
        for i in range(1, 2*rho+1): B /= (1-z0**i*V)
        A += B
    # twist correction (N = 2 mod 4): eps^r lam^{2r} = (c u)^r puts eps into u, i.e. phi -> phi - pi/N inside V,
    # but the Gaussian i phi^2/tau is not invariant under that shift: extra factor e^{-i q phi/theta - i pi q/(2 theta N)}
    # (completing the square: zeta^{r^2} eps^r = zeta0^{r^2} e^{2 pi i theta (r - q/(2theta))^2/(qN)} e^{-i pi q/(2 theta N)}; see report_P1b.md)
    tw = exp(SGN*1j*q*fs/theta - 1j*pi*q/(2*theta*N)) if N % 4 == 2 else 1
    return tw*Cf*sqrt(2*pi*tau/(-g2))/(q*tau)*A*exp(g(fs)/tau)
SGN = -1   # VERIFIED sign (SGN=+1 does not converge)
if __name__ == '__main__':
    p, q, theta = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for N in [int(x) for x in sys.argv[4:]]:
        while (p*N+theta) % q or gcd((p*N+theta)//q, N) != 1: N += 1
        a = (p*N+theta)//q
        S, u, eps = exact_sigma(a, N, q)
        ms = range(0, 2*theta) if theta > 0 else range(0, 2*theta, -1)
        parts = [predict(p, q, theta, N, u, m, eps) for m in ms]  # twist rule: extra (-1)^m when N=2 mod 4 (found empirically)
        tot = sum(parts)
        print('N', N, 'N%4', N % 4, 'a', a, '|S|/sqrtN', nstr(abs(S)/sqrt(N), 6), 'S/pred', nstr(S/tot, 8),
              '|parts|/|S|', [nstr(abs(x/S), 3) for x in parts], flush=True)
