# P1e_renorm.py -- VERIFIED (mpmath): the single-saddle amplitude renormalises to the level-q object.
#   lim_{d->0, N->inf, n2->inf} S_amp(p/q; x, N) = (1-w_q)^{-1/(2q)} Z_q(p/q)      (Lemma R of P1e_lemma.tex, PROVED there)
# Z_q computed two independent ways: (a) psi-series of exp(Phi_q), (b) Sigma_q / (G*_q e^{-Phi_q(eps)}) with Sigma_q direct.
# S_amp computed as in P1d (Definition 4) at x = p/q + theta/(qN) with n2 terms.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1e_renorm.py p q N n2
import sys
from mpmath import mp, mpf, mpc, exp, pi, log, nstr, findroot, sqrt
from math import gcd
mp.dps = 50
def E(y): return exp(2j*pi*y)
def level(a, N):
    x = mpf(a)/N; z = E(x); c = -2*(1-z); C = c**N; w = 1/C
    for _ in range(200): w = (1-w)**2/C
    lam2 = exp(2*log(1-w)/N); return x, z, c, w, lam2/c
def Zq_psi(p, q, nt=400):
    x, z, c, w, u = level(p, q)
    a = [mpc(0)]*(nt+1)
    for n in range(1, nt+1):
        if n % q: a[n] = u**n/(n*(1-z**(-n)))
    # psi = exp(sum a_n Y^n):  n psi_n = sum_k k a_k psi_{n-k}
    psi = [mpc(1)] + [mpc(0)]*nt
    for n in range(1, nt+1): psi[n] = sum(k*a[k]*psi[n-k] for k in range(1, n+1))/n
    return sum(psi[n]*z**(-n*n) for n in range(nt+1)), w, u, abs(psi[nt])
def Zq_direct(p, q):
    x, z, c, w, u0 = level(p, q)
    n0 = 1 if q % 4 == 2 else 0; eps = E(mpf(-n0)/q); u = eps*u0; l2 = u*c
    S = mpc(0); T = mpc(1)
    for r in range(q):
        S += z**(r*r)*T; T = T*l2/((1-z**(2*r+1)*u)*(1-z**(2*r+2)*u))
    G = sum(E(mpf(p*r*r - n0*r)/q) for r in range(q))
    Ph = sum(u0**n/n*eps**n/(1-z**(-n)) for n in range(1, 3000) if n % q)
    return S/(G*exp(-Ph))
def Samp(p, q, N, n2, th=1):
    while (p*N+th) % q or gcd((p*N+th)//q, N) != 1: N += 1
    a = (p*N+th)//q
    x, z, c, w, u0 = level(a, N)
    z0 = E(mpf(p)/q); U = u0**q
    t0 = findroot(lambda t: 1j*pi*t+log(1-U*E(-q*t))/q, mpc(0))
    W0 = U*E(-q*t0); S = mpc(0)
    for k in range(q):
        gk = sum(z0**(-nu*nu-k*nu) for nu in range(q))/q
        B = -log(1-W0)/(2*q) + sum(u0**n/(n*(1-z**(-n)))*z0**(k*n)*E(-n*t0) for n in range(1, n2+1) if n % q)
        S += gk*exp(B)
    return S, W0, N
p, q, N, n2 = map(int, sys.argv[1:5])
Zp, wq, uq, lastpsi = Zq_psi(p, q)
Zd = Zq_direct(p, q)
S, W0, NN = Samp(p, q, N, n2)
pred = (1-wq)**(-mpf(1)/(2*q))*Zp
print('%d/%d  Z_q(psi)=%s  Z_q(direct)=%s  |diff|=%s  | S_amp(N=%d,n2=%d)=%s  pred=%s  |S/pred-1|=%s  |W0-w_q|=%s' % (
    p, q, nstr(Zp, 12), nstr(Zd, 12), nstr(abs(Zp-Zd), 3), NN, n2, nstr(S, 12), nstr(pred, 12), nstr(abs(S/pred-1), 3), nstr(abs(W0-wq), 3)))
