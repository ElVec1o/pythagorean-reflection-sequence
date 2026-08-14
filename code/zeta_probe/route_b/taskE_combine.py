#!/usr/bin/env python3
"""
COMBINED van der Corput bound, window [a, Y0=2W], split into:
  (S) |y-y*|<=d:  vdC-2:  |int_S| <= 8 * lambda_s^{-1/2} (sup_S A + Var_S A),  lambda_s=inf_S|Phi''|
  (F) flanks [a,y*-d] and [y*+d,Y0]: vdC-1 (IBP):
        |int A e^{iPhi}| <= |A(b)/Phi'(b)| + |A(a)/Phi'(a)| + int |d/dy (A/Phi')| dy
      <= (sup_F A)/m  + (1/m)(Var_F A) + (sup_F A) Var(1/Phi')  ... we just compute the IBP
      directly: int A e^{iPhi} dy = [A/(iPhi') e^{iPhi}] - int (A/(iPhi'))' e^{iPhi},
      |.| <= |A/Phi'|_endpoints + int |(A/Phi')'| dy. We bound by:
        |int_F| <= 2 sup_F|A/Phi'| + Var_F(A/Phi').
We MEASURE the actual sup/Var inputs over each piece (high precision) and form the constant.
We choose d = D * sqrt(W) (Gaussian width scale). Optimize D.
"""
import mpmath as mp
mp.mp.dps = 60
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def B_series(s, tau, N=45):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpc(0)
    for n in range(1,N+1):
        p=2*n
        def Sf(a):
            c=mp.mpf(a)/2
            return 2**p*(mp.bernpoly(p+1,(s-1)+1+c)-mp.bernpoly(p+1,c))/(p+1)
        Q=Sf(2)+Sf(1)-((s-1)+1)
        tot+=f[n]*tau**(2*n)*Q
    return tot
def AP(y, W, tau):
    g=1-mp.e**(-B_series(mp.mpc(0,1)*y, tau))
    A=abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    Phi=2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
    return A,Phi
def amp(y,W,tau): return AP(y,W,tau)[0]
def phid(y,W,tau,h=mp.mpf('1e-6')):  # Phi'
    return (AP(y+h,W,tau)[1]-AP(y-h,W,tau)[1])/(2*h)
def phidd(y,W,tau,h=mp.mpf('1e-5')):
    return (AP(y+h,W,tau)[1]-2*AP(y,W,tau)[1]+AP(y-h,W,tau)[1])/h**2

def piecewise_bound(tau, D, Ngrid=400):
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; st=mp.sqrt(tau)
    a=mp.mpf('0.5'); Y0=2*W; d=D*mp.sqrt(W)
    yL=ys-d; yR=ys+d
    # (S) saddle window [yL,yR]
    lam_s=mp.inf; supAs=mp.mpf(0); VarAs=mp.mpf(0); prev=None
    for k in range(Ngrid+1):
        y=yL+(yR-yL)*mp.mpf(k)/Ngrid
        lam_s=min(lam_s,abs(phidd(y,W,tau))); av=amp(y,W,tau); supAs=max(supAs,av)
        if prev is not None: VarAs+=abs(av-prev)
        prev=av
    boundS=8/mp.sqrt(lam_s)*(supAs+VarAs)
    # flanks: F = [a,yL] U [yR,Y0]
    def flank(lo,hi):
        # bound |int A e^{iPhi}| <= 2 sup|A/Phi'| + Var(A/Phi')
        prev=None; sup=mp.mpf(0); Var=mp.mpf(0)
        for k in range(Ngrid+1):
            y=lo+(hi-lo)*mp.mpf(k)/Ngrid
            v=amp(y,W,tau)/abs(phid(y,W,tau))
            sup=max(sup,v)
            if prev is not None: Var+=abs(v-prev)
            prev=v
        return 2*sup+Var
    boundFL=flank(a,yL); boundFR=flank(yR,Y0)
    total=boundS+boundFL+boundFR
    return total/st, boundS/st, (boundFL+boundFR)/st, float(lam_s), float(d), float(W)

print("Combined vdC bound /sqrt(tau), Y0=2W, d=D sqrt(W).  Optimize D.")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
    print(f"\ntau={float(tau)}:")
    for D in [mp.mpf('1.5'),mp.mpf('2.0'),mp.mpf('2.5'),mp.mpf('3.0')]:
        tot,bS,bF,lam,d,W=piecewise_bound(tau,D)
        print(f"  D={float(D)}: total={mp.nstr(tot,5)} sqrtT  (saddle={mp.nstr(bS,4)}, flanks={mp.nstr(bF,4)})  lam_s={lam:.4f} d={d:.2f}")
