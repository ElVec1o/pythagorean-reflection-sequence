# P1f_zpm.py -- numerics (VERIFIED, floating mpmath): Z_N = sum psi_k zeta^{-k^2} and the shifted sums
# Z^{pm} = sum psi_k zeta^{-k^2 -+ k} that appear as amplitudes of S_pm (P1f Task C). psi_k: e^{Phi(Y)} = sum psi_k Y^k,
# Phi(Y) = sum_{N !| n} u0^n Y^n /(n (1 - zeta^{-n})),  u0 = lambda^2/c.
from mpmath import mp, mpc, exp, pi, log, sqrt, fabs, nstr
import sys
from math import gcd
mp.dps = 30
def e(y): return exp(2j*pi*y)
def setup(a, N):
    z = e(mp.mpf(a)/N); c = -2*(1-z); X = c**N; B = 2+X
    w = 2/(B*(1+sqrt(1-4/(B*B))))
    if fabs(w) >= 1: w = 1/w
    lam2 = exp(2*log(1-w)/N); u0 = lam2/c
    return z, c, w, u0
def psi(a, N, K):
    z, c, w, u0 = setup(a, N)
    ph = [mpc(0)]*(K+1)
    for n in range(1, K+1):
        if n % N: ph[n] = u0**n/(n*(1-z**(-n)))
    # exp of power series: psi' = Phi' psi
    ps = [mpc(0)]*(K+1); ps[0] = mpc(1)
    for k in range(1, K+1):
        ps[k] = sum(j*ph[j]*ps[k-j] for j in range(1, k+1))/k
    return z, ps
if __name__ == '__main__':
    for (a, N) in [(1,3),(2,5),(1,4),(3,8),(3,7),(2,7),(1,5),(4,9),(5,11),(7,17),(5,13)]:
        K = 400
        z, ps = psi(a, N, K)
        Z = sum(ps[k]*z**(-k*k) for k in range(K+1))
        Zp = sum(ps[k]*z**(-k*k-k) for k in range(K+1))
        Zm = sum(ps[k]*z**(-k*k+k) for k in range(K+1))
        print('%d/%d |Z|=%s |Z+|=%s |Z-|=%s  Z+/Z=%s  Z-/Z=%s' % (a, N, nstr(abs(Z),6), nstr(abs(Zp),6), nstr(abs(Zm),6), nstr(Zp/Z,6), nstr(Zm/Z,6)))
