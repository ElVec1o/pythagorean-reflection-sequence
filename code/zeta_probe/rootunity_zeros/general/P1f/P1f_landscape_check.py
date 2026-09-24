# P1f_landscape_check.py -- VERIFIED (floating, sampled; NOT a certificate): sanity check of the analytic landscape
# inequalities of P1f_lemma.tex (Lemma LS) with the exact exponent  W_mu(x) = Re((Phi(x) + 2 pi i mu x/N) e^{-i theta}),
# Phi(x) = x L - x^2 - Li2(e^{-2Nx})/N^2 + pi^2/(6N^2), on the central tie ray theta*, for all explicit modes |mu|<=2N
# (paths [x_A, x_mu] U x_mu + e^{i theta/2}[0,inf)) and on the remainder rays gamma_-+ (directions theta -+ pi/8, modes -+2N).
# Reports: T, max over non-dominant pieces of W - T (must be < 0), dominant-segment max of (W-T)/sigma^2 (must be < 0),
# and the head exponent bound H_head of Lemma HD.
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, polylog, atan, cos, sin, nstr, sqrt
mp.dps = 20
def run(a, N, samples=120):
    z = exp(2j*pi*mpf(a)/N); c = -2*(1-z); L = log(c); ell = L.real; phi = L.imag
    X = c**N; Bq = 2+X; w = 2/(Bq*(1+sqrt(1-4/(Bq*Bq)))); xi = log(1-w)/N
    s = 1 if N % 2 else 2
    surv = lambda m: (N % 2 == 1) or (N % 4 == 0 and m % 2 == 0) or (N % 4 == 2 and m % 2 == 1)
    n = min((m for m in range(-2*N, 2*N) if surv(m)), key=lambda m: abs(phi + 2*pi*(m + mpf(s)/2)/N))
    th = atan((phi + 2*pi*(n + mpf(s)/2)/N)/ell); E = exp(-1j*th)
    Om = lambda x, mu: x*L - x*x - polylog(2, exp(-2*N*x))/N**2 + pi**2/(6*N*N) + 2j*pi*mu*x/N
    W = lambda x, mu: (Om(x, mu)*E).real
    xm = lambda mu: (L + 2j*pi*mu/N)/2 - xi
    T = W(xm(n), n)
    delta = mpf(1)/(8*N); worst_nd = -1e9; worst_dom = -1e9; worst_rem = -1e9
    for xA_abs in (delta/2, delta, 2*delta):
        xA = xA_abs*exp(1j*th)
        for mu in range(-2*N, 2*N+1):
            if not surv(mu): continue
            X0 = xm(mu)
            for i in range(samples+1):
                sg = mpf(i)/samples; x = X0 - sg*(X0 - xA); v = W(x, mu) - T
                if mu in (n, n+s):
                    if sg > 0: worst_dom = max(worst_dom, v/sg**2)
                else: worst_nd = max(worst_nd, v)
            for i in range(1, samples+1):
                vv = 3*mpf(i)/samples; x = X0 + vv*exp(1j*th/2); v = W(x, mu) - T
                if mu in (n, n+s): worst_dom = max(worst_dom, v/vv**2)
                else: worst_nd = max(worst_nd, v)
        for sgn, mu in ((-1, -2*N), (1, 2*N+1)):
            if not surv(mu): mu += sgn
            for i in range(samples+1):
                rr = 4*mpf(i)/samples; x = xA + rr*exp(1j*(th + sgn*pi/8)); worst_rem = max(worst_rem, W(x, mu) - T)
    head = delta*(ell + 0.1) + (2*delta/N)*(1 + log(1/(1.8*delta)))
    return float(th*180/pi), float(T), float(worst_nd), float(worst_dom), float(worst_rem), float(head)
if __name__ == '__main__':
    Ns = [int(v) for v in sys.argv[1:]]
    for N in Ns:
        for a in range(1, N):
            if gcd(a, N) != 1 or not (N <= 5*a <= 4*N): continue
            th, T, nd, dom, rem, hd = run(a, N)
            flag = 'OK' if (nd < 0 and dom < 0 and rem < 0 and hd < T) else 'VIOLATION'
            print('%d/%d th*=%.2f T=%.4f max(W-T) nondom=%.4f  dom (W-T)/sig^2<=%.4f  rem=%.4f  head=%.4f  %s' % (a, N, th, T, nd, dom, rem, hd, flag), flush=True)
