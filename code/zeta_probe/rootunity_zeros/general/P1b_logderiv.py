# P1b item (2): the level-q quantities an inductive error bound needs. At the surviving saddle phi_{m0}
# (m0=0 for q odd or 4|q, m0=1 for q=2 mod 4), with V = u0 e^{2 i phi}, u0 = -1/(2(1-zeta0)):
#   A(phi) = sum_{rho<q} T_rho,  T_rho = zeta0^{rho^2} e^{2 i rho phi}/(zeta0 V;zeta0)_{2 rho}.
# Reports D1 = |A'|/(q|A|), D2 = |A''|/(q^2|A|), E = sum|T_rho|/|A| and |A|/sqrt q.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1b_logderiv.py QMAX [DELTA]
import sys
from math import gcd
from mpmath import mp, mpf, mpc, exp, pi, log, sqrt, sin, findroot, nstr
mp.dps = 40
def data(p, q):
    z0 = exp(2j*pi*p/q); u = -1/(2*(1-z0)); U = u**q
    f0 = findroot(lambda f: 2j*f - (mpf(2)/q)*log(1-U*exp(2j*q*f)), mpc(0, 0.01))
    m0 = 1 if q % 4 == 2 else 0
    fs = f0 + pi*m0/q; V = u*exp(2j*fs)
    A = A1 = A2 = mpc(0); env = mpf(0)
    T = mpc(1); S1 = mpc(0); S2 = mpc(0)       # T_rho, sum s_i, sum s_i(1+s_i) over i<=2rho
    for rho in range(q):
        Tr = z0**(rho*rho)*exp(2j*rho*fs)*T
        L1 = 2j*rho + 2j*S1; L2 = -4*S2
        A += Tr; A1 += Tr*L1; A2 += Tr*(L1*L1 + L2); env += abs(Tr)
        for i in (2*rho+1, 2*rho+2):
            x = z0**i*V; s = x/(1-x); S1 += s; S2 += s*(1+s); T /= (1-x)
    return abs(A1)/(q*abs(A)), abs(A2)/(q*q*abs(A)), env/abs(A), abs(A)/sqrt(q)
QMAX = int(sys.argv[1]); DELTA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
mx = [0, 0, 0]; mn = 1e9; arg = [None]*4
for q in range(2, QMAX+1):
    for p in range(1, q//2+1):
        if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(DELTA): continue
        d1, d2, e, a = data(p, q)
        for k, v in enumerate((d1, d2, e)):
            if v > mx[k]: mx[k] = v; arg[k] = (p, q)
        if a < mn: mn = a; arg[3] = (p, q)
    if q % 25 == 0: print('q', q, 'max D1 %.4f %s  max D2 %.4f %s  max E %.4f %s  min |A|/sqrt q %.4f %s' % (mx[0], arg[0], mx[1], arg[1], mx[2], arg[2], mn, arg[3]), flush=True)
