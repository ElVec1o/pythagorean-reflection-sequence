# P1a: limiting level-q saddle amplitude  Gcal(p/q, theta, N mod 4q|theta|) = sum_m e^{-i pi m^2 N/(2 q theta)} W_m,
# W_m = C(phi_m) A(phi_m) (see report_P1a.md). Sigma(a/N) ~ Pref * e^{g0/tau} * Gcal, a/N = p/q + theta/(qN).
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1a_amp.py QMAX THMAX [DELTA]
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, sin, findroot, nstr
mp.dps = 30
def weights(p, q, theta):
    z0 = exp(2j*pi*p/q); u = -1/(2*(1-z0)); U = u**q
    dg = lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f))
    f0 = findroot(dg, mpc(0, 0.01))
    ms = list(range(0, 2*theta)) if theta > 0 else list(range(0, 2*theta, -1))
    W = []
    for m in ms:
        fs = f0 + pi*m/q; V = u*exp(2j*fs)
        Cf = sqrt((1-V**q)/(1-U))
        for i in range(1, q+1): Cf *= ((1-z0**i*u)/(1-z0**i*V))**(mpf(i)/q)
        A = mpc(0)
        for rho in range(q):
            B = z0**(rho*rho)*exp(2j*rho*fs)
            for i in range(1, 2*rho+1): B /= (1-z0**i*V)
            A += B
        W.append(Cf*A)
    return ms, W
def gcal(p, q, theta, n):
    ms, W = weights(p, q, theta)
    return sum(exp(-1j*pi*m*m*n/(2*q*theta))*w for m, w in zip(ms, W)), sum(abs(w) for w in W)
if __name__ == '__main__':
    QMAX, THMAX = int(sys.argv[1]), int(sys.argv[2]); DELTA = float(sys.argv[3]) if len(sys.argv) > 3 else 0.05
    worst = []
    for q in range(2, QMAX+1):
        for p in range(1, q//2+1):
            if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(DELTA): continue
            for theta in [t for t in range(-THMAX, THMAX+1) if t != 0]:
                ms, W = weights(p, q, theta); nrm = sum(abs(w) for w in W)
                mn = None
                for n in range(1, 4*q*abs(theta), 2):
                    if (p*n+theta) % q: continue
                    G = sum(exp(-1j*pi*m*m*n/(2*q*theta))*w for m, w in zip(ms, W))
                    r = abs(G)/nrm
                    if mn is None or r < mn[0]: mn = (r, n)
                if mn: worst.append((float(mn[0]), p, q, theta, mn[1]))
        print('q', q, 'done', flush=True)
    worst.sort()
    print('cases', len(worst)); print('smallest |Gcal|/sum|W_m|:')
    for w in worst[:15]: print('  %.5f  p/q=%d/%d theta=%d  N=%d mod 4q|theta|' % w)
