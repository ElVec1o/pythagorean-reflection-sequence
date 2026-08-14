#!/usr/bin/env python3
"""
Gather the van der Corput inputs over the SADDLE WINDOW around y*=W/2.
We bound |T2| by splitting:
  T2 = int_0^{Y0} integrand dy  + Tail,
  Tail = sum_{i>Y0}(-1)^i psi(i)  bounded by factorial decay (NOT the divergent AP integral).
On [0,Y0] (Y0 a fixed multiple of y*, away from pole pi/tau), apply vdC 2nd-deriv test.

Inputs needed (numerically, uniformly in tau):
 (1) lambda = inf_{[0,Y0]} |Phi''|   (Phi'' < 0 throughout? where is it smallest in modulus?)
 (2) sup|A| on [0,Y0]
 (3) Var(A) = int_0^{Y0} |A'| dy  on [0,Y0]
 (4) Tail bound.
Phi'(y)=2 log(W/(2y)) is monotone DECREASING (Phi'>0 for y<y*, <0 for y>y*), single saddle.
For the 2nd-deriv test we need |Phi''|>=lambda on the WHOLE window. But Phi''=-4/W*(y*/y)... ~ -2/y.
Actually Phi'(y)~2 log(W/2y) => Phi''(y) ~ -2/y, which -> 0 as y->inf but is LARGE near 0.
On [a, Y0] with a>0, |Phi''|>= 2/Y0 (min at the right end). Let's MEASURE.
"""
import mpmath as mp
mp.mp.dps = 50
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def B_series(s, tau, N=40):
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
def g_iy(y, tau): return 1-mp.e**(-B_series(mp.mpc(0,1)*y, tau))
def A_phase(y, W, tau):
    g=g_iy(y,tau)
    A=abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    Phi=2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
    return A,Phi

print("Window [a,Y0] around y*=W/2.  Measure inf|Phi''|, sup A, Var(A)=int|A'|.")
print(f"{'tau':>8} {'y*':>7} {'Y0=4y*':>7} {'inf|Phi`'+chr(39)+'|':>10} {'supA':>11} {'VarA':>11} {'A(Y0)':>11}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.005']]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2
    a=mp.mpf('0.3'); Y0=4*ys     # window: small a>0 (avoid 1/sinh blowup at 0) to 4 y*
    def Ph(y): return A_phase(y,W,tau)[1]
    def Aamp(y): return A_phase(y,W,tau)[0]
    h=mp.mpf('1e-5')
    def P2(y): return (Ph(y+h)-2*Ph(y)+Ph(y-h))/h**2
    # scan |Phi''| min on [a,Y0]
    infP2=mp.inf; supA=mp.mpf(0); 
    N=120; ys_=float(ys)
    grid=[a+(Y0-a)*mp.mpf(k)/N for k in range(N+1)]
    Avals=[]
    for y in grid:
        infP2=min(infP2, abs(P2(y)))
        av=Aamp(y); supA=max(supA,av); Avals.append(av)
    # Var(A) approx = sum |A_{k+1}-A_k|
    VarA=sum(abs(Avals[k+1]-Avals[k]) for k in range(len(Avals)-1))
    print(f"{float(tau):>8} {float(ys):>7.3f} {float(Y0):>7.2f} {mp.nstr(infP2,4):>10} "
          f"{mp.nstr(supA,5):>11} {mp.nstr(VarA,5):>11} {mp.nstr(Aamp(Y0),4):>11}")
