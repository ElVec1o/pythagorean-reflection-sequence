#!/usr/bin/env python3
"""
The CORRECT van der Corput object is the AP integrand on s=iy:
   integrand(y) = -A(y) sin Phi(y),
   A(y)=|g_{iy}| sqrt(coth(pi y)/(pi y)),  Phi(y)=2y log W + arg g_{iy} - arg Gamma(1+2iy).
Phi'(y) ~ 2 log(W/(2y)),  stationary at y*=W/2,  Phi''(y*) ~ -4/W.
T2 = int_0^inf integrand(y) dy  (formal; diverges on tail, but the SADDLE WINDOW is fine).

Here we VERIFY: (a) Phi'(y*)=0, Phi''(y*)=-4/W; (b) on the saddle window the partial integral
matches T2; (c) the amplitude A(y) near the saddle and its behavior.
We use fast B_series for g_{iy} (valid y<pi/tau).
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
        def S(a):
            c=mp.mpf(a)/2
            return 2**p*(mp.bernpoly(p+1,(s-1)+1+c)-mp.bernpoly(p+1,c))/(p+1)
        Q=S(2)+S(1)-((s-1)+1)
        tot+=f[n]*tau**(2*n)*Q
    return tot

def g_iy(y, tau):
    B=B_series(mp.mpc(0,1)*y, tau)
    return 1-mp.e**(-B)
def A_phase(y, W, tau):
    g=g_iy(y,tau)
    A=abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    Phi=2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
    return A, Phi
def integrand(y, W, tau):
    A,Phi=A_phase(y,W,tau)
    return -A*mp.sin(Phi)

for tau in [mp.mpf('0.1'),mp.mpf('0.02')]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2
    # Phi' and Phi'' by FD on the smooth Phi
    h=mp.mpf('1e-6')
    def Ph(y): return A_phase(y,W,tau)[1]
    P1=(Ph(ys+h)-Ph(ys-h))/(2*h)
    P2=(Ph(ys+h)-2*Ph(ys)+Ph(ys-h))/h**2
    print(f"tau={float(tau)}: y*=W/2={float(ys):.4f}  Phi'(y*)={mp.nstr(P1,5)} (~0)  "
          f"Phi''(y*)={mp.nstr(P2,6)} vs -4/W={mp.nstr(-4/W,6)}")
    A_ys,_=A_phase(ys,W,tau)
    print(f"   A(y*)={mp.nstr(A_ys,6)}  saddle lead A(y*)sqrt(2pi/|Phi''|)={mp.nstr(A_ys*mp.sqrt(2*mp.pi/abs(P2)),6)}"
          f"  =0.0389 sqrt(tau)? {mp.nstr(A_ys*mp.sqrt(2*mp.pi/abs(P2))/mp.sqrt(tau),6)}")
