# P1g_inherit_check.py -- VERIFIED (floating mpmath): inheritance of Z^pm and omega from a seed j/n to a/N in its
# neighbourhood.  Prints Z^pm_N/Z_N vs Z^pm_n(j/n)/Z_n(j/n) and omega_N vs omega_n.
import sys
sys.path.insert(0, '../P1f')
from mpmath import mp, nstr, fabs
from P1f_zpm import psi, setup
mp.dps = 30
def zs(a, N, K):
    z, ps = psi(a, N, K)
    _, c, w, u0 = setup(a, N)
    Z = sum(ps[k]*z**(-k*k) for k in range(K+1)); Zp = sum(ps[k]*z**(-k*k-k) for k in range(K+1))
    Zm = sum(ps[k]*z**(-k*k+k) for k in range(K+1))
    return Z, Zp, Zm, Zm/(u0*Zp)
for (j, n) in [(1,3),(2,5),(3,7),(4,11)]:
    K = 700
    Z0, P0, M0, om0 = zs(j, n, K)
    print('seed %d/%d  Z+/Z=%s Z-/Z=%s omega=%s' % (j, n, nstr(P0/Z0,8), nstr(M0/Z0,8), nstr(om0,8)))
    for k in (20, 60, 150):
        for (a, N) in [(j*k+ (1 if n==3 else 0), n*k+1)]:
            from math import gcd
            # pick a with |a/N - j/n| = 1/(nN)
            for aa in range(1, N):
                if gcd(aa, N) == 1 and abs(aa*n - j*N) == 1: a = aa; break
            Z, P, M, om = zs(a, N, K)
            print('   %d/%d d=%s  Z+/Z=%s Z-/Z=%s omega=%s |dom|=%s' % (a, N, nstr(mp.mpf(a)/N-mp.mpf(j)/n,3), nstr(P/Z,8), nstr(M/Z,8), nstr(om,8), nstr(fabs(om-om0),3)))
