# P2_heads.py -- the block model amplitudes (HEURISTIC model, values exact finite sums):
#   N even: B ~ H e^{eps s/(N^2 t)},  H = sum_{rho<N/2} c^rho zeta^{rho^2}/(zeta;zeta)_{2rho}
#   N odd : B ~ H_e cosh(s/(N^2 t)) + H_o sinh(s/(N^2 t)),  s = c^{N/2} (either root),
#           H_e = sum_{rho<=(N-1)/2} c^rho zeta^{rho^2}/(zeta;zeta)_{2rho},
#           H_o = s^{-1} sum_{kappa=(N+1)/2}^{N-1} c^kappa zeta^{kappa^2}/(zeta;zeta)_{2kappa-N}
# usage: python3 P2_heads.py a N [a N ...]
import sys
from mpmath import mp, mpc, exp, pi, sqrt, nstr, fabs, log
mp.dps = 40
def heads(a, N):
    z = exp(2j*pi*a/N); c = -2*(1-z)
    def poch(m):
        p = mpc(1)
        for j in range(1, m+1): p *= (1-z**j)
        return p
    s = sqrt(c**N) if N % 2 else c**(N//2)
    He = sum(c**r*z**(r*r)/poch(2*r) for r in range((N-1)//2+1)) if N % 2 else sum(c**r*z**(r*r)/poch(2*r) for r in range(N//2))
    Ho = (sum(c**k*z**(k*k)/poch(2*k-N) for k in range((N+1)//2, N))/s) if N % 2 else None
    return z, c, s, He, Ho
args = sys.argv[1:]
for i in range(0, len(args), 2):
    a, N = int(args[i]), int(args[i+1]); z, c, s, He, Ho = heads(a, N)
    if N % 2 == 0:
        eps = 1 if N % 4 == 0 else -1
        print('%d/%d even: V_lead=%s  |H|=%s  log|H|=%s' % (a, N, nstr(eps*s/N**2, 10), nstr(abs(He), 8), nstr(log(abs(He)), 8)))
    else:
        A1, A2 = (He+Ho)/2, (He-Ho)/2
        print('%d/%d odd : V_lead=+-%s  |A+|=%s |A-|=%s  (A+ goes with e^{+s/(N^2 t)})' % (a, N, nstr(s/N**2, 10), nstr(abs(A1), 8), nstr(abs(A2), 8)))
