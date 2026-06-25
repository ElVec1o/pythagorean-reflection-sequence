#!/usr/bin/env python3
# Debug the swap.  Check S_in(x) closed form vs brute sum_j p^j/(-c p^j e^{ix};p)_inf.
import mpmath as mp
mp.mp.dps=30
def qpoch_inf(a,p,tol=mp.mpf(10)**(-35),NM=200000):
    r=mp.mpc(1);ai=a
    for i in range(NM):
        r*=(1-ai);ai*=p
        if abs(ai)<tol:break
    return r
def S_in_closed(x,c,p,N=600):
    e=mp.e**(1j*x);poch=(1-p);t=mp.mpc(1)/poch;s=t
    for n in range(1,N):
        t=t*(-c*e)*(1-p**n)/(1-p**(n+1));s+=t
        if abs(t)<mp.mpf(10)**(-40) and n>10:break
    return s
def S_in_brute(x,c,p,J=4000):
    e=mp.e**(1j*x);s=mp.mpc(0)
    for j in range(J):
        s+=p**j/qpoch_inf(-c*p**j*e,p)
        if p**j<mp.mpf(10)**(-40):break
    return s
tau=mp.mpf("0.2");q=mp.e**(-tau);p=q*q;c=2*q**2*(1-q)
for x in [mp.mpf("0.0"),mp.mpf("0.5"),mp.mpf("1.3")]:
    a=S_in_closed(x,c,p);b=S_in_brute(x,c,p)
    print(f"x={mp.nstr(x,3)}  closed={mp.nstr(a,14)}  brute={mp.nstr(b,14)}  diff={mp.nstr(a-b,4)}")
print()
# Also: directly test  Sigma = 2q sum_j p^j Phi(p^j z2) with Phi via IZ-int, NO swap.
def Phi_IZ(y,p,q,T=40):
    pp=qpoch_inf(p,p);p32=qpoch_inf(p**mp.mpf(1.5),p);logp2=-4* (-mp.log(q))
    C0=(pp/p32)/mp.sqrt(mp.pi*(-logp2));pinf=qpoch_inf(p,p)
    def integ(xx):
        e=mp.e**(1j*xx)
        return (mp.e**(xx*xx/logp2)/(pinf*qpoch_inf(-p*e,p)*qpoch_inf(-q*y*e,p))).real
    return C0*mp.quad(integ,[-T,0,T])
def Sigma_direct(tau,K=400):
    q=mp.e**(-tau);p=q*q;u=2*q/(1-p);s=u
    for k in range(K):
        u*=-2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)));s+=u
        if abs(u)<mp.mpf(10)**(-40) and k>20:break
    return s
z2=2*q*(1-q)
Jmax=int(mp.ceil(50/(-mp.log10(p))))+3
Snoswap=2*q*mp.fsum([p**j*Phi_IZ(p**j*z2,p,q) for j in range(Jmax)])
print("Sigma direct       =",mp.nstr(Sigma_direct(tau),16))
print("Sigma 2q sum p^j Phi_IZ (no swap) =",mp.nstr(Snoswap,16))
