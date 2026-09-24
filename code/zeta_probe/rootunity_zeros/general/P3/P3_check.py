# P3_check.py -- VERIFIED-level checks (mpmath floating, high precision) for P3_note.tex.
# (1) Gauss identities: G^+ = G^- and B^- - B^+ = G0 (exact identities, checked numerically);
# (2) Galois invariance Omega(zeta^j lam) = Omega(lam);
# (3) 2-adic claim v(omega - sigma omega) = 3/2 via the rational norm: v_2 N_{Q(zeta,w)/Q}(omega-sigma omega) = 3 phi(N).
import sys
from fractions import Fraction
from math import gcd
from mpmath import mp, mpf, exp, pi, log, sqrt, nstr, mpc, fabs, re, im, nint
mp.dps=int(sys.argv[1])
def e(y): return exp(2j*pi*y)
def Omega(z,N,c,lam):
    u0=lam**2/c; q=1/z; Tp=0; Tm=0; P=mpc(1)
    for s in range(N):
        if s>0: P*=(1-lam*q**s)
        Tp+=z**(-s*s-s)*u0**s/P; Tm+=z**(-s*s+s)*u0**s/P
    return Tm/(u0*Tp)
def roots(z,N):
    c=-2*(1-z); X=c**N; B=2+X; d=sqrt(B*B-4)
    return c,(B-d)/2,(B+d)/2
for N in [int(x) for x in sys.argv[2:]]:
    a=1; z=e(mpf(a)/N)
    G0=sum(z**(-s*s) for s in range(N)); Gp=sum(z**(-s*s-s) for s in range(N)); Gm=sum(z**(-s*s+s) for s in range(N))
    es=lambda s: sum(z**(-i) for i in range(1,s+1))
    Bp=sum(z**(-s*s-s)*es(s) for s in range(N)); Bm=sum(z**(-s*s+s)*es(s) for s in range(N))
    print('N',N,'|G+-G-|',nstr(abs(Gp-Gm),3),'|B- - B+ - G0|',nstr(abs(Bm-Bp-G0),3))
    c,w1,w2=roots(z,N); lam=exp(log(1-w1)/N)
    print('   invariance max', nstr(max(abs(Omega(z,N,c,lam*z**j)-Omega(z,N,c,lam)) for j in range(N)),3))
    prod=mpc(1)
    for b in range(1,N):
        if gcd(b,N)!=1: continue
        zb=e(mpf(b)/N); cb,u1,u2=roots(zb,N)
        o1=Omega(zb,N,cb,exp(log(1-u1)/N)); o2=Omega(zb,N,cb,exp(log(1-u2)/N))
        prod*= -(o1-o2)**2
    # identify rational: prod should be real rational; find denominator by continued fraction
    x=re(prod)
    fr=Fraction(str(nstr(x, mp.dps-20))).limit_denominator(10**(mp.dps//3))
    err=abs(x-mpf(fr.numerator)/fr.denominator)
    num,den=fr.numerator,fr.denominator
    v=0
    while num%2==0 and num: num//=2; v+=1
    while den%2==0: den//=2; v-=1
    phi=sum(1 for k in range(1,N) if gcd(k,N)==1)
    print('   Norm(omega-sigma omega) ~', nstr(x,15),'imag',nstr(im(prod),3),'rational fit err',nstr(err,3),'den bits',fr.denominator.bit_length(),'v2 =',v,' 3phi(N) =',3*phi)
