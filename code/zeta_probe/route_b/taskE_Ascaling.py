#!/usr/bin/env python3
"""Correct empirical scaling of A(y*) and sup_S A, Var_S A over the window."""
import mpmath as mp
mp.mp.dps = 50
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def Bser(s, tau, N=40):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpc(0)
    for n in range(1,N+1):
        p=2*n; c1=mp.mpf('0.5'); c2=mp.mpf('1.0')
        S2=2**p*(mp.bernpoly(p+1,s+c2)-mp.bernpoly(p+1,c2))/(p+1)
        S1=2**p*(mp.bernpoly(p+1,s+c1)-mp.bernpoly(p+1,c1))/(p+1)
        tot+=f[n]*tau**(2*n)*(S2+S1-s)
    return tot
def A(y,W,tau):
    g=1-mp.e**(-Bser(mp.mpc(0,1)*y,tau))
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))

print("A(y*) at the TRUE saddle, and sup_S A over window |y-y*|<=D sqrt(W), D=2.5:")
print(f"{'tau':>9} {'A(y*)':>12} {'A(y*)/tau^.75':>13} {'supS A':>12} {'supS/tau^.75':>12} {'Var/sup':>8}")
D=mp.mpf('2.5')
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002'),mp.mpf('0.001')]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; d=D*mp.sqrt(W)
    Ays=A(ys,W,tau)
    # window sup and Var
    yL=ys-d; yR=ys+d
    sup=mp.mpf(0); Var=mp.mpf(0); prev=None; N=200
    for k in range(N+1):
        y=yL+(yR-yL)*mp.mpf(k)/N; v=A(y,W,tau); sup=max(sup,v)
        if prev is not None: Var+=abs(v-prev)
        prev=v
    t34=tau**mp.mpf('0.75')
    print(f"{float(tau):>9} {mp.nstr(Ays,6):>12} {mp.nstr(Ays/t34,6):>13} {mp.nstr(sup,6):>12} "
          f"{mp.nstr(sup/t34,6):>12} {mp.nstr(Var/sup,4):>8}")
# the saddle A(y*) scaling: from saddle, A(y*)=|g_{s*}| sqrt(coth/pi y*). |g_s*|=sqrt2/36 sqrt(tau).
# sqrt(coth(pi y*)/(pi y*)) ~ 1/sqrt(pi y*) = 1/sqrt(pi W/2). W=sqrt(2/tau) => y*~ (1/2)sqrt(2/tau)
# 1/sqrt(pi y*) = 1/sqrt(pi/2 sqrt(2/tau)) = (tau/2)^{1/4}/sqrt(pi/2... ) -> A(y*) ~ tau^{1/2}*tau^{1/4}=tau^{3/4}. ok
c1=mp.sqrt(2)/36
print(f"\npredicted A(y*) = c1 sqrt(tau) * 1/sqrt(pi*W/2):")
for tau in [mp.mpf('0.01'),mp.mpf('0.001')]:
    W=mp.sqrt(2/tau)*mp.e**(-tau/2)
    pred=c1*mp.sqrt(tau)/mp.sqrt(mp.pi*W/2)
    print(f"  tau={float(tau)}: A(y*) pred={mp.nstr(pred,6)}  /tau^.75={mp.nstr(pred/tau**mp.mpf('.75'),6)}")
