# P3_explore.py -- floating exploration (HEURISTIC/VERIFIED only): omega(a/N)=Z^-/(u0 Z^+) along a/N -> seed.
import sys; sys.path.insert(0,'../P1f')
from P1f_zpm import psi, setup
from mpmath import mp, nstr, mpf
def omega(a,N,K):
    z,c,w,u0 = setup(a,N)
    _,ps = psi(a,N,K)
    Zp = sum(ps[k]*z**(-k*k-k) for k in range(K+1))
    Zm = sum(ps[k]*z**(-k*k+k) for k in range(K+1))
    return Zm/(u0*Zp)
mp.dps=int(sys.argv[1]); K=int(sys.argv[2])
p,q = int(sys.argv[3]), int(sys.argv[4])
from math import gcd
print('seed',p,q, nstr(omega(p,q,K),12))
for N in [int(x) for x in sys.argv[5:]]:
    for a in [ (p*N+1)//q, (p*N-1)//q+ (1 if (p*N-1)%q else 0)]:
        pass
    for a in range(p*N//q-1, p*N//q+3):
        if gcd(a,N)!=1: continue
        d = mpf(a)/N - mpf(p)/q
        if abs(d)*N*q > 1.01: continue
        print(N,a, nstr(d,5), nstr(omega(a,N,K),12))
