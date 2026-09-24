# P1f_model.py -- VERIFIED (floating mpmath) checks of the P1f saddle model at zeta = e(a/N):
#   B(zeta e^{-t}) ~ kappa * sum_m A(m) e^{V_m/t},   A(m) = e^{x_m lin} (1-w)^{-1/(2N)} G*(m) Z_N,
#   V_m = L_m^2/4 + pi^2/(6N^2) - xi^2 - Li2(w)/N^2,  x_m = L_m/2 - xi,  L_m = L + 2 pi i m/N,  xi = Log(1-w)/N,
#   kappa = C_zeta sqrt((1-w)/(2N(1+w))),  C_zeta = prod_{i<N} (1-zeta^i)^{-(1/2 - i/N)},  lin = zeta/(1-zeta).
# Usage: python3 P1f_model.py a N  r theta_deg [mmin mmax]
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, polylog, nstr, fsum
import sys
from math import gcd
def e(y): return exp(2j*pi*y)
def setup(a, N):
    z = e(mpf(a)/N); c = -2*(1-z); L = log(c); X = c**N; Bq = 2+X
    w = 2/(Bq*(1+sqrt(1-4/(Bq*Bq))))
    if abs(w) >= 1: w = 1/w
    xi = log(1-w)/N
    lin = z/(1-z)
    Cz = mpc(1)
    for i in range(1, N): Cz *= (1-z**i)**(-(mpf(1)/2 - mpf(i)/N))
    kap = Cz*sqrt((1-w)/(2*N*(1+w)))
    return z, c, L, w, xi, lin, kap
def Gstar(a, N, m): return fsum(e(mpf(a*r*r - m*r)/N) for r in range(N))
def ZN(a, N, K=None):
    z, c, L, w, xi, lin, kap = setup(a, N)
    u0 = exp(2*xi)/c
    if K is None: K = int(mp.dps*2.4/(-log(abs(u0)))) + 20
    ph = [mpc(0)]*(K+1)
    for n in range(1, K+1):
        if n % N: ph[n] = u0**n/(n*(1-z**(-n)))
    ps = [mpc(0)]*(K+1); ps[0] = mpc(1)
    for k in range(1, K+1): ps[k] = fsum(j*ph[j]*ps[k-j] for j in range(1, k+1))/k
    return fsum(ps[k]*z**(-k*k) for k in range(K+1))
def model_terms(a, N, ms):
    z, c, L, w, xi, lin, kap = setup(a, N); Z = ZN(a, N)
    out = {}
    for m in ms:
        Lm = L + 2j*pi*m/N; xm = Lm/2 - xi
        V = Lm*Lm/4 + pi**2/(6*N*N) - xi*xi - polylog(2, w)/N**2
        A = exp(xm*lin)*(1-w)**(-mpf(1)/(2*N))*Gstar(a, N, m)*Z
        out[m] = (kap*A, V)
    return out
def Bser(q):
    s = mpc(1); poch = mpc(1); aa = -2*(1-q); k = 1; big = mpf(1)
    while True:
        poch *= (1-q**(2*k-1))*(1-q**(2*k)); term = aa**k*q**(k*k)/poch; s += term; big = max(big, abs(term))
        if k > 10 and abs(term) < mpf(10)**(-mp.dps+3)*big: return s, big
        k += 1
if __name__ == '__main__':
    a, N = int(sys.argv[1]), int(sys.argv[2]); r = mpf(sys.argv[3]); th = mpf(sys.argv[4])*pi/180
    mmin, mmax = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (-2*N, 2*N)
    mp.dps = 30 + int(3/float(r))
    t = r*exp(1j*th); z = e(mpf(a)/N)
    B, big = Bser(z*exp(-t))
    terms = model_terms(a, N, range(mmin, mmax+1))
    mod = fsum(A*exp(V/t) for (A, V) in terms.values())
    hs = sorted(((float((V*exp(-1j*th)).real), m) for m, (A, V) in terms.items() if abs(A) > 1e-20), reverse=True)
    print('%d/%d r=%s th=%s: |B|=%s  B/model=%s  top heights %s  max|b_k|~e^%.3g/r' % (a, N, nstr(r,4), nstr(th*180/pi,5), nstr(abs(B),5), nstr(B/mod,8), [(round(h,4), m) for h, m in hs[:3]], float(log(big)*r)))
