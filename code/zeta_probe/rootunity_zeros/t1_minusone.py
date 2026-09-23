# t1_minusone.py -- floating-point (mpmath) numerics for paper2a prop:t1minusone / cor:Uminusone.
# At the zeros q*_j=-e^{-t*_j} of 1-Sigma_1 near q=-1: S_e against its saddle asymptotic, t1 two ways
# (P12/S_e and -(1+S_-/S_e)/2), (t1-phi)/t (-> -phi/10), 1-g t1, and the junction pairings at x=+-sqrt(q).
# 'generic' checks P12 = -(S_e+S_-)/2 off the zeros.  Usage: python3 t1_minusone.py generic | j1 j2 ...  (NOT a certificate)
# numerics at zeros q*_j of g=1-Sigma_1 near q=-1 (paper2a prop:minusone)
from mpmath import mp, mpf, mpc, exp, log, pi, findroot, sqrt, nstr, atan, polylog
import sys
def sums(q):
    # g, S_e, S_-, Y3  as q-series
    g=mpc(0);Se=mpc(0);Sm=mpc(0);Y=mpc(0); p2=mpc(1); a=mpc(1); b=mpc(1); big=mpf(1); j=0
    eps=mpf(10)**(-mp.dps-5)
    while True:
        if j>0: p2*=(1-q**(2*j-1))*(1-q**(2*j))
        c=(-2*(1-q))**j/p2
        tg=c*q**(j*j); ts=tg*q**j; tm=tg*q**(-j)
        ty=(-2)**j*(1-q)**j*q**(j*j+3*j)/(a*b)
        a*=(1-q**(2*j+2)); b*=(1-q**(2*j+5))
        g+=tg; Se+=ts; Sm+=tm; Y+=ty
        mm=max(abs(tg),abs(ts),abs(tm),abs(ty)); big=max(big,mm); j+=1
        if j>30 and mm<eps*big: break
    return g,Se,Sm,Y,big
phi=(1+sqrt(5))/2
if sys.argv[1]=='generic':
    mp.dps=40
    for q in [mpf('0.3'), mpc('-0.5','0.4'), mpc('0.1','-0.7')]:
        g,Se,Sm,Y,big=sums(q); P12=2*q**3/(1-q**3)*Y
        print('q',q,' P12+ (Se+Sm)/2 =',nstr(P12+(Se+Sm)/2,5),' |g|',nstr(abs(g),5))
    sys.exit()
L=log(4); th1=atan(pi/L); x0=log(2+sqrt(5))/2
Lp=lambda t: log(2*(1+exp(-t)))
for j in [int(v) for v in sys.argv[1:]]:
    t0=(L+1j*pi)/(2*j+mpf(3)/2)
    mp.dps=40+int(1.5/abs(t0)/2.3)
    tm=t0
    for it in range(80): tm=(Lp(tm)+1j*pi)/(2*j+1)
    Phi0=x0*L-x0**2-polylog(2,exp(-4*x0))/4+pi**2/24
    tz=findroot(lambda tt: sums(-exp(-tt))[0]*exp(-Phi0/tt), tm, tol=mpf(10)**(-mp.dps+20))
    q=-exp(-tz); g,Se,Sm,Y,big=sums(q)
    x=sqrt(q)  # principal branch, near +i
    P12=2*q**3/(1-q**3)*Y; t1=P12/Se; t1b=-(1+Sm/Se)/2
    Ep=Phi0-pi**2/4+1j*pi*L/2
    pred=-1j*exp(-1j*pi/4)*(5*phi**7)**(-mpf(1)/4)*exp(Ep/tz)
    gU=q/(1-q**2); gV=q/(1-q)
    out=[]
    for xx in (x,-x):
        PiU=2*q*(1+xx)/(1-xx)/(1-gU*t1)*(t1*(1-xx+q)/(1+q)+1/(2*xx))
        PiV=2*q*(1+xx)/(1-q)/(1-gV*t1)*(t1+(1+xx)/(2*xx))
        out.append((PiU,PiV))
    print('j',j,'|t|',nstr(abs(tz),5),'argdiff',nstr(mp.arg(tz)-th1,3),'dps',mp.dps)
    print('   |g|/big',nstr(abs(g)/big,3),' |Se|/big',nstr(abs(Se)/big,3),' Se/pred',nstr(Se/pred,10))
    print('   t1',nstr(t1,15),' t1-t1b',nstr(abs(t1-t1b),3),' (t1-phi)/t',nstr((t1-phi)/tz,10))
    print('   1-gU t1',nstr(1-gU*t1,8),' 1-gV t1',nstr(1-gV*t1,8))
    print('   PiU(+x)',nstr(out[0][0],10),' PiU(-x)',nstr(out[1][0],10))
    print('   PiV(+x)',nstr(out[0][1],10),' PiV(-x)',nstr(out[1][1],10), flush=True)
