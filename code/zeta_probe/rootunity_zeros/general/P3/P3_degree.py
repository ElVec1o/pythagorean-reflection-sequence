# P3_degree.py -- VERIFIED-level (floating, PSLQ): algebraic degree of t1*=-(1+omega)/2 over Q.
# Usage: python P3_degree.py <dps> <K> a1/N1 [a2/N2 ...]
# IMPORTANT: |u0| ~ 0.27-0.29, so the defining series converges slowly; use K >= 15*N (K >= 15*max(N))
# for a reliable findpoly/PSLQ result. K=30-60 under-converges for N>~4 and reads as a false negative.
import sys; sys.path.insert(0,'../P1f')
from P1f_zpm import psi, setup
from mpmath import mp, nstr, findpoly, mpf, re, im
mp.dps=int(sys.argv[1]); K=int(sys.argv[2])
for arg in sys.argv[3:]:
    a,N = map(int,arg.split('/'))
    if K < 15*N:
        print(f'WARNING: K={K} < 15*N={15*N} for {arg}; series may be under-converged (false negative risk)', file=sys.stderr)
    z,c,w,u0 = setup(a,N); _,ps = psi(a,N,K)
    Zp = sum(ps[k]*z**(-k*k-k) for k in range(K+1)); Zm = sum(ps[k]*z**(-k*k+k) for k in range(K+1))
    om = Zm/(u0*Zp); t1 = -(1+om)/2
    # minimal polynomial of the real number Re(t1) and |t1|^2 etc; use t1 + conj via re part and im part
    found=None
    for deg in range(1,25):
        p = findpoly(re(t1), deg, maxcoeff=10**12)
        if p: found=(deg,p); break
    print(arg, nstr(t1,20), 'Re t1 minpoly:', found)
