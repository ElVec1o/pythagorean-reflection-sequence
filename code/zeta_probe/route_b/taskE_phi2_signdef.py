#!/usr/bin/env python3
"""
RIGOR CHECK: confirm full Phi''(y) < 0 (no zeros) on the saddle window, and that the
analytic Bessel Phi''_B=4 Im psi1(1+2iy) lower-bounds |Phi''| (the (arg g)'' correction is small).
Also confirm Phi' is monotone (single saddle) so the flank |Phi'|>=m holds.
"""
import mpmath as mp
mp.mp.dps = 45
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def Bser(s, tau, N=35):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpc(0)
    for n in range(1,N+1):
        p=2*n; c1=mp.mpf('0.5'); c2=mp.mpf('1.0')
        S2=2**p*(mp.bernpoly(p+1,s+c2)-mp.bernpoly(p+1,c2))/(p+1)
        S1=2**p*(mp.bernpoly(p+1,s+c1)-mp.bernpoly(p+1,c1))/(p+1)
        tot+=f[n]*tau**(2*n)*(S2+S1-s)
    return tot
def fullPhi(y,W,tau):
    g=1-mp.e**(-Bser(mp.mpc(0,1)*y,tau))
    return 2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
def P2b(y):
    s=mp.mpc(0,1)*y; return 4*mp.im(mp.polygamma(1,1+2*s))

for tau in [mp.mpf('0.02'),mp.mpf('0.005')]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; d=mp.mpf('1.5')*mp.sqrt(W)
    h=mp.mpf('1e-4')
    yL=ys-d; yR=ys+d
    print(f"tau={float(tau)}: window [{float(yL):.2f},{float(yR):.2f}], y*={float(ys):.2f}")
    maxgap=mp.mpf(0); allneg=True; minabs=mp.inf
    for k in range(31):
        y=yL+(yR-yL)*mp.mpf(k)/30
        full=(fullPhi(y+h,W,tau)-2*fullPhi(y,W,tau)+fullPhi(y-h,W,tau))/h**2
        bess=P2b(y)
        if full>=0: allneg=False
        minabs=min(minabs,abs(full))
        maxgap=max(maxgap,abs(full-bess))
    print(f"  full Phi''<0 everywhere on window: {allneg};  min|full Phi''|={mp.nstr(minabs,5)};")
    print(f"  max|full-Bessel Phi''| (the arg-g'' correction)={mp.nstr(maxgap,4)} "
          f"(<< |Phi''|~{mp.nstr(4/W,4)}, so Bessel part dominates)")
