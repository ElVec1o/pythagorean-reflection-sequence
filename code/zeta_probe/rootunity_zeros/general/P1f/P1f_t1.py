# P1f_t1.py -- VERIFIED (floating mpmath): at zeros q* = zeta e^{-t*} of B on the central tie ray, compare
#   t1(q*) = -(1 + S_-/S_e)/2   with the predicted limit  t1* = -(1+omega)/2,  omega = Z^-_N/(u0 Z^+_N),
# and evaluate the transfer factors 1-g_U t1, 1-g_V t1, Pi_1, Pi_q (paper2a eq:RJclosed1, eq:RJclosedq) at both roots x.
import sys
from mpmath import mp, mpf, mpc, exp, pi, log, findroot, nstr, arg, atan, sqrt, fsum
from P1f_model import setup, model_terms, Bser, e
from P1f_zpm import psi
def Spm(q, sgn):
    s = mpc(1); poch = mpc(1); aa = -2*(1-q); k = 1; big = mpf(1)
    while True:
        poch *= (1-q**(2*k-1))*(1-q**(2*k)); term = aa**k*q**(k*k + sgn*k)/poch; s += term; big = max(big, abs(term))
        if k > 10 and abs(term) < mpf(10)**(-mp.dps+3)*big: return s
        k += 1
def omega(a, N):
    mp.dps = 30
    z, ps = psi(a, N, 500)
    Zp = fsum(ps[k]*z**(-k*k-k) for k in range(501)); Zm = fsum(ps[k]*z**(-k*k+k) for k in range(501))
    zz, c, L, w, xi, lin, kap = setup(a, N); u0 = exp(2*xi)/c
    return Zm/(u0*Zp), Zp, Zm
def factors(q, t1):
    gU = q/(1-q*q); gV = q/(1-q); out = [1-gU*t1, 1-gV*t1]
    for x in (sqrt(q), -sqrt(q)):
        P1 = 2*q*(1+x)/(1-q)*(t1 + (1+x)/(2*x))/(1-gV*t1)
        Pq = 2*q*(1+x)/((1-x)*(1-gU*t1))*(t1*(1-x+q)/(1+q) + 1/(2*x))
        out += [P1, Pq]
    return out
if __name__ == '__main__':
    a, N = int(sys.argv[1]), int(sys.argv[2]); js = [int(v) for v in sys.argv[3:]]
    om, Zp, Zm = omega(a, N); t1s = -(1+om)/2; zeta = e(mpf(a)/N)
    lim = factors(zeta, t1s)
    print('%d/%d |Z+|=%s |Z-|=%s omega=%s t1*=%s' % (a, N, nstr(abs(Zp),5), nstr(abs(Zm),5), nstr(om,8), nstr(t1s,8)))
    print('   limits: 1-gU t1=%s 1-gV t1=%s | x=+sqrt: Pi1=%s Piq=%s | x=-sqrt: Pi1=%s Piq=%s' % tuple(nstr(v,5) for v in lim))
    s = 1 if N % 2 else 2
    zz, c, L, w, xi, lin, kap = setup(a, N); ell = L.real; phi = L.imag
    best = None
    for n in range(-3*N, 3*N):
        if abs(model_terms(a, N, [n])[n][0]) < 1e-20: continue
        th = atan((phi + 2*pi*(n + mpf(s)/2)/N)/ell)
        if best is None or abs(th) < abs(best[1]): best = (n, th)
    n, th = best
    T = model_terms(a, N, [n, n+s]); dV = T[n+s][1]-T[n][1]; rho = T[n+s][0]/T[n][0]
    for j in js:
        cands = sorted([(abs((log(-1/rho)+2j*pi*k)/dV), (log(-1/rho)+2j*pi*k)/dV) for k in range(-j-3, j+4)
                        if ((log(-1/rho)+2j*pi*k)/dV).real > 0 and abs(arg((log(-1/rho)+2j*pi*k)/dV)+th) < 0.3], key=lambda v: v[0])
        u0_ = cands[j-1][1]; t0 = 1/u0_
        mp.dps = 30 + int(4/abs(t0))
        ts = findroot(lambda tt: Bser(zeta*exp(-tt))[0], (t0, t0*(1+mpf(10)**-6)), solver='secant', tol=mpf(10)**-25, maxsteps=40)
        q = zeta*exp(-ts); Se = Spm(q, 1); Sm = Spm(q, -1); t1 = -(1 + Sm/Se)/2
        f = factors(q, t1)
        print('  j=%d |t*|=%s t1=%s |t1-t1*|/|t*|=%s  factors %s' % (j, nstr(abs(ts),4), nstr(t1,8), nstr(abs(t1-t1s)/abs(ts),4), [nstr(v,4) for v in f]), flush=True)
        mp.dps = 30
