# P3_degree.py -- VERIFIED-level (floating, PSLQ): algebraic degree of t1*=-(1+omega)/2 over Q.
import sys; sys.path.insert(0,'../P1f')
from P1f_zpm import psi, setup
from mpmath import mp, nstr, findpoly, mpf, re, im
mp.dps=int(sys.argv[1]); K=int(sys.argv[2])
for arg in sys.argv[3:]:
    a,N = map(int,arg.split('/'))
    z,c,w,u0 = setup(a,N); _,ps = psi(a,N,K)
    Zp = sum(ps[k]*z**(-k*k-k) for k in range(K+1)); Zm = sum(ps[k]*z**(-k*k+k) for k in range(K+1))
    om = Zm/(u0*Zp); t1 = -(1+om)/2
    # minimal polynomial of the real number Re(t1) and |t1|^2 etc; use t1 + conj via re part and im part
    found=None
    for deg in range(1,25):
        p = findpoly(re(t1), deg, maxcoeff=10**12)
        if p: found=(deg,p); break
    print(arg, nstr(t1,20), 'Re t1 minpoly:', found)
