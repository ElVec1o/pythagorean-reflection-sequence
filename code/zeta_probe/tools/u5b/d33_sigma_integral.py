#!/usr/bin/env python3
# Combine: Sigma = 2q sum_{j>=0} p^j Phi(p^j z^2), z^2=2q(1-q),
# with Phi(y) = C0 * INT exp(-x^2/4tau)/[(p;p)_inf (-p e^{ix};p)_inf (-q y e^{ix};p)_inf] dx.
# Swap sum and integral (justified: dominated, Gaussian * absolutely-summable-in-j since |p^j Phi| bounded).
#   Sigma = 2q C0 INT exp(-x^2/4tau)/[(p;p)_inf (-p e^{ix};p)_inf]
#                 * sum_{j>=0} p^j / (-q p^j z^2 e^{ix};p)_inf  dx
# The inner sum  S_in(x) = sum_{j>=0} p^j / (-c p^j e^{ix};p)_inf,  c=q z^2 = q*2q(1-q)=2q^2(1-q).
# Use q-binomial: 1/(t;p)_inf = sum_{n>=0} t^n/(p;p)_n.  So
#   1/(-c p^j e^{ix};p)_inf = sum_n (-c e^{ix})^n p^{jn}/(p;p)_n
#   S_in = sum_n (-c e^{ix})^n/(p;p)_n sum_j p^{j(n+1)} = sum_n (-c e^{ix})^n/[(p;p)_n (1-p^{n+1})]
#        = sum_n (-c e^{ix})^n/(p;p)_{n+1}.
# That's a clean closed inner factor.  Let's just verify the SINGLE integral for Sigma numerically.
import mpmath as mp
mp.mp.dps = 30

def qpoch_inf(a,p,tol=mp.mpf(10)**(-35),NM=200000):
    r=mp.mpf(1) if not isinstance(a,complex) else mp.mpc(1)
    ai=a
    for i in range(NM):
        r*=(1-ai); ai*=p
        if abs(ai)<tol: break
    return r

def Sigma_direct(tau,K=400):
    q=mp.e**(-tau);p=q*q;u=2*q/(1-p);s=u
    for k in range(K):
        u*=-2*(1-q)*q**(2*k+3)/((1-q**(2*k+4))*(1-q**(2*k+3)));s+=u
        if abs(u)<mp.mpf(10)**(-40) and k>20:break
    return s

def S_in(x,c,p,N=400):
    # sum_n (-c e^{ix})^n/(p;p)_{n+1}
    e=mp.e**(1j*x); s=mp.mpc(0); pn=mp.mpf(1)  # (p;p)_{n+1} built iteratively, start (p;p)_1=1-p
    poch=(1-p)  # (p;p)_1
    term0=mp.mpc(1)/poch
    s=term0; t=term0
    for n in range(1,N):
        t = t * (-c*e) / (1-p**(n+1))  # ratio term_n/term_{n-1} = (-c e)*(p;p)_n/(p;p)_{n+1} = -c e/(1-p^{n+1})
        s+=t
        if abs(t)<mp.mpf(10)**(-40) and n>10:break
    return s

def Sigma_IZint(tau,T=40):
    q=mp.e**(-tau);p=q*q
    pp=qpoch_inf(p,p);p32=qpoch_inf(p**mp.mpf(1.5),p)
    logp2=-4*tau
    C0=(pp/p32)/mp.sqrt(mp.pi*(-logp2))
    pinf=qpoch_inf(p,p)
    c=2*q**2*(1-q)   # = q*z^2
    def integ(x):
        e=mp.e**(1j*x)
        den=pinf*qpoch_inf(-p*e,p)
        val=mp.e**(-x*x/(4*tau))/den*S_in(x,c,p)
        return val.real
    val=mp.quad(integ,[-T,0,T])
    return 2*q*C0*val

for tau in [mp.mpf("0.2"),mp.mpf("0.1"),mp.mpf("0.05")]:
    Sd=Sigma_direct(tau);Si=Sigma_IZint(tau)
    print(f"tau={mp.nstr(tau,3):>6}  Sigma_direct={mp.nstr(Sd,16):>20}  Sigma_int={mp.nstr(Si,16):>20}  diff={mp.nstr(Sd-Si,4)}")
