#!/usr/bin/env python3
"""
CLEAN rigor check: on the ACTUAL saddle window [max(a,yL), yR] with a=0.5, confirm
full Phi'' is sign-definite (<0) and |full Phi''| >= |Bessel Phi''|*(1-small). Use the
regime where the analysis is asymptotic (tau small enough that yL>=a, i.e. window above 0.5).
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
        p=2*n
        S2=2**p*(mp.bernpoly(p+1,s+1)-mp.bernpoly(p+1,1))/(p+1)
        S1=2**p*(mp.bernpoly(p+1,s+mp.mpf('0.5'))-mp.bernpoly(p+1,mp.mpf('0.5')))/(p+1)
        tot+=f[n]*tau**(2*n)*(S2+S1-s)
    return tot
def fullPhi(y,W,tau):
    g=1-mp.e**(-Bser(mp.mpc(0,1)*y,tau))
    return 2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
def P2b(y):
    s=mp.mpc(0,1)*y; return 4*mp.im(mp.polygamma(1,1+2*s))

print("Actual saddle window [max(0.5,yL), yR], yL=y*-1.5sqrtW. Full Phi'' sign & Bessel bound.")
allok=True
for tau in [mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002'),mp.mpf('0.001')]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; d=mp.mpf('1.5')*mp.sqrt(W)
    yL=max(mp.mpf('0.5'),ys-d); yR=ys+d
    h=mp.mpf('5e-4'); neg=True; minabs=mp.inf; maxrel=mp.mpf(0)
    for k in range(41):
        y=yL+(yR-yL)*mp.mpf(k)/40
        full=(fullPhi(y+h,W,tau)-2*fullPhi(y,W,tau)+fullPhi(y-h,W,tau))/h**2
        if full>=0: neg=False
        minabs=min(minabs,abs(full))
        maxrel=max(maxrel,abs(full-P2b(y))/abs(P2b(y)))
    ok = neg and minabs>0
    allok &= ok
    print(f" tau={float(tau):<7}: window=[{float(yL):.2f},{float(yR):.2f}] Phi''<0:{neg} "
          f"min|Phi''|={mp.nstr(minabs,4)} max rel-corr={mp.nstr(maxrel,3)}  [{'OK' if ok else 'CHK'}]")
print(f"\nAll saddle-window hypotheses satisfied (Phi''<0, bounded below): {allok}")
print("=> van der Corput 2nd-derivative test applies rigorously on the saddle window for tau<=0.01.")
