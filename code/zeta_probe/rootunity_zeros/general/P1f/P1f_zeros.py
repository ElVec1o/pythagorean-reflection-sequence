# P1f_zeros.py -- VERIFIED (floating mpmath): zeros of B(zeta e^{-t}) near the predicted two-saddle zeros on the
# central tie ray (the tie ray with the smallest |theta|).  u_j solves 1 + rho e^{dV u} = 0, rho = A(n+s)/A(n).
# Usage: python3 P1f_zeros.py a N j1 j2 ...
import sys
from mpmath import mp, mpf, mpc, exp, pi, log, findroot, nstr, arg, atan
from P1f_model import setup, model_terms, Bser, e
a, N = int(sys.argv[1]), int(sys.argv[2]); js = [int(v) for v in sys.argv[3:]]
mp.dps = 30
s = 1 if N % 2 else 2
z, c, L, w, xi, lin, kap = setup(a, N)
ell = L.real; phi = L.imag
best = None
for n in range(-3*N, 3*N):
    terms = model_terms(a, N, [n, n+s])
    if abs(terms[n][0]) < 1e-20: continue
    th = atan((phi + 2*pi*(n + mpf(s)/2)/N)/ell)
    if best is None or abs(th) < abs(best[1]): best = (n, th)
n, th = best
terms = model_terms(a, N, [n, n+s]); (A1, V1), (A2, V2) = terms[n], terms[n+s]
dV = V2 - V1; rho = A2/A1; T = (V1*exp(-1j*th)).real
print('%d/%d tie pair (%d,%d) theta*=%s deg  T=%s  |dV|=%s  Re(dV e^{-i th})=%s' % (a, N, n, n+s, nstr(th*180/pi, 6), nstr(T, 6), nstr(abs(dV), 6), nstr((dV*exp(-1j*th)).real, 3)))
for j in js:
    # zeros of 1 + rho e^{dV u}: dV u = log(-1/rho) + 2 pi i k; pick k with arg u ~ -theta*
    cands = []
    for k in range(-j-3, j+4):
        u = (log(-1/rho) + 2j*pi*k)/dV
        if u.real > 0: cands.append((abs(arg(u) + th), abs(u), u))
    cands = [cd for cd in cands if cd[0] < 0.3]; cands.sort(key=lambda v: v[1])
    if len(cands) < j: print('  j=%d: not enough candidates' % j); continue
    u0 = cands[j-1][2]; t0 = 1/u0
    mp.dps = 30 + int(4/abs(t0))
    try:
        ts = findroot(lambda tt: Bser(z*exp(-tt))[0], (t0, t0*(1+mpf(10)**-6)), solver='secant', tol=mpf(10)**-25, maxsteps=40)
        print('  j=%d t0=%s |t0|=%s arg=%s  t*=%s  |1/t*-u0|*|dV|=%s  |t*-t0|/|t0|^2=%s' % (j, nstr(t0, 8), nstr(abs(t0), 4), nstr(arg(t0)*180/pi, 5), nstr(ts, 10), nstr(abs(1/ts-u0)*abs(dV), 4), nstr(abs(ts-t0)/abs(t0)**2, 4)), flush=True)
    except Exception as ex: print('  j=%d fail %s' % (j, str(ex)[:60]))
    mp.dps = 30
