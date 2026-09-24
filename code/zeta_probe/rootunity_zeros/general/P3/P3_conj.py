# P3_conj.py -- floating check: omega via the finite formula T^-/(u0 T^+) at lambda (physical root, |w|<1)
# vs sigma(omega): same formula at the Galois-conjugate w'=1/w (any N-th root lambda' of 1-w').
import sys
from mpmath import mp, mpf, exp, pi, log, sqrt, nstr, mpc, fabs
mp.dps=int(sys.argv[1])
def e(y): return exp(2j*pi*y)
def om(z,N,c,lam):
    u0=lam**2/c; q=1/z
    Tp=0; Tm=0; P=mpc(1)
    for s in range(N):
        if s>0: P*= (1-lam*q**s)
        Tp+= z**(-s*s-s)*u0**s/P; Tm+= z**(-s*s+s)*u0**s/P
    return Tm/(u0*Tp)
for arg in sys.argv[2:]:
    a,N=map(int,arg.split('/'))
    z=e(mpf(a)/N); c=-2*(1-z); X=c**N; B=2+X
    w=2/(B*(1+sqrt(1-4/(B*B))))
    if fabs(w)>=1: w=1/w
    lam=exp(log(1-w)/N)
    wp=1/w; lamp=exp(log(1-wp)/N)
    o1=om(z,N,c,lam); o2=om(z,N,c,lamp); o3=om(z,N,c,lamp*z)
    print(arg,'omega',nstr(o1,12),'sigma',nstr(o2,12),'check-indep',nstr(abs(o2-o3),3))
