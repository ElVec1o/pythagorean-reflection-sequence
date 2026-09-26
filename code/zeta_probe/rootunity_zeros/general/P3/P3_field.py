# P3_field.py -- VERIFIED-level (floating PSLQ): is t1*(zeta) in Q(zeta, w)?  (w: root of c^N w=(1-w)^2)
# Usage: python P3_field.py <dps> <K> a1/N1 [a2/N2 ...]
# IMPORTANT: since |u0| ~ 0.27-0.29, the series psi_k u0^k converges slowly; K must be roughly
# 15*N or more (K >= 15*max(N)) for PSLQ to see a reliable relation at the given precision.
# K=30-60 (the values used in earlier runs) silently under-converges for N>~4 and can look
# like "no relation found" even though one exists -- that is a false negative, not a refutation.
import sys; sys.path.insert(0,'../P1f')
from P1f_zpm import psi, setup
from mpmath import mp, nstr, pslq, re, im, sqrt
from math import gcd
def phi(n): return sum(1 for k in range(1,n+1) if gcd(k,n)==1)
mp.dps=int(sys.argv[1]); K=int(sys.argv[2])
for arg in sys.argv[3:]:
    a,N = map(int,arg.split('/'))
    if K < 15*N:
        print(f'WARNING: K={K} < 15*N={15*N} for {arg}; series may be under-converged (false negative risk)', file=sys.stderr)
    z,c,w,u0 = setup(a,N); _,ps = psi(a,N,K)
    Zp = sum(ps[k]*z**(-k*k-k) for k in range(K+1)); Zm = sum(ps[k]*z**(-k*k+k) for k in range(K+1))
    t1 = -(1+Zm/(u0*Zp))/2
    basis=[z**i*w**j for j in range(2) for i in range(phi(N))]
    v=[t1]+basis
    wt=sqrt(2)+mp.pi/7
    rel=pslq([re(x)+wt*im(x) for x in v], maxcoeff=10**15, maxsteps=10**6)
    ok=None
    if rel:
        res=sum(r*x for r,x in zip(rel,v)); ok=nstr(abs(res),5)
    print(arg, 'relation:',rel,'residual',ok)
