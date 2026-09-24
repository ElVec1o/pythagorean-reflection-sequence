# P1d_check.py -- VERIFIED (mpmath, floating high precision; not a proof): Z_N(x) (Theorem 1, by its psi-series) against the
# single-saddle main term Main'(x) of P1d_lemma.tex (Definition 4), printing err = |Z/Main' - 1| and err/|d|.
# Shows err ~ K(p/q)|d|, independent of N and of N mod 4.  (Main' here uses n2=60 for the A-set; d<0 by the direct formula
# with alpha = -arg(F'')/2, which agrees with the conjugation definition.)
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1d_check.py p q N1 N2 ...
from mpmath import mp, mpf, mpc, exp, pi, log, nstr, polylog, findroot, sqrt, arg
from math import gcd
import sys
def Zseries(a,N,NT,dps):
    mp.dps=dps
    z=exp(2j*pi*mpf(a)/N); c=-2*(1-z); C=c**N; w=1/C
    for _ in range(50): w=(1-w)**2/C
    lam=(1-w)**(mpf(1)/N); u=lam**2/c
    psi=[mpc(1), u*z*(1+z)/(z**2-1)*1]  # check n=1 via recurrence below instead
    psi=[mpc(1)]; pm2=mpc(0)
    # recurrence psi_n (z^{2n}-1) = u z^{2n-1}(1+z) psi_{n-1} - u^2 z^{2n-1} psi_{n-2}, valid n<N (and 2n not = 0 mod N)
    for n in range(1,NT):
        z2n1=z**(2*n-1)
        prev2=psi[n-2] if n>=2 else mpc(0)
        psi.append((u*z2n1*(1+z)*psi[n-1]-u*u*z2n1*prev2)/(z**(2*n)-1))
    Z=sum(psi[n]*z**(-n*n) for n in range(NT))
    return Z,u,z,max(abs(p) for p in psi),abs(psi[-1])
def mainZ(p,q,a,N,u,z,n2=60):
    mp.dps=40
    x=mpf(a)/N; d=x-mpf(p)/q; sg=1 if d>0 else -1
    z0=exp(2j*pi*mpf(p)/q); U=u**q
    F=lambda t: 1j*pi*t**2/2+polylog(2,U*exp(-2j*pi*q*t))/(2j*pi*q*q)
    t0=findroot(lambda t: 1j*pi*t+log(1-U*exp(-2j*pi*q*t))/q, mpc(0))
    W=U*exp(-2j*pi*q*t0); F2=1j*pi+2j*pi*W/(1-W)
    al=(pi-arg(F2))/2 if sg>0 else -arg(F2)/2
    S=mpc(0)
    for k in range(q):
        gk=sum(z0**(-nu*nu-k*nu) for nu in range(q))/q
        Y=z0**k*exp(-2j*pi*t0)
        B=-log(1-W)/(2*q)+sum((u**n/n)*z**n/(z**n-1)*Y**n for n in range(1,n2+1) if n%q)
        S+=gk*exp(B)
    M=exp(1j*(al-pi*sg/4))*sqrt(pi/abs(F2))*exp(F(t0)/d)*S
    return M,S,F(t0),t0
p,q=int(sys.argv[1]),int(sys.argv[2])
for arg_ in sys.argv[3:]:
    N=int(arg_)
    for th in (1,-1,2,-2,5,-7,20,-20):
        if (p*N+th)%q: continue
        a=(p*N+th)//q
        if gcd(a,N)!=1: continue
        d=mpf(th)/(q*N)
        NT=int(8/float(abs(d))**0.5)+200
        Z,u,z,mx,last=Zseries(a,N,min(NT,N-1),int(60+30/float(abs(d))**0.5))
        M,S,F0,t0=mainZ(p,q,a,N,u,z)
        r=Z/M
        print('N',N,'th',th,'d',nstr(d,4),'Z/M',nstr(r,10),'err',nstr(abs(r-1),4),'err/|d|',nstr(abs(r-1)/abs(d),4),'|S|',nstr(abs(S),6),'maxpsi',nstr(mx,3),'last',nstr(last,3),flush=True)
