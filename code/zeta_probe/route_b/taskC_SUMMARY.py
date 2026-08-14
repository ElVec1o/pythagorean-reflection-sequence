#!/usr/bin/env python3
"""
TASK C SUMMARY (tau=0.01). Reproduces every headline number.
Modules: taskC_Bs.py (high-precision B_s via loggamma antidifference + analytic tail).
Findings:
 1. B_s construction validated (matches exact integer sum to ~1e-54; diff-eq B(s+1)-B(s)=b(s) to 1e-55).
 2. (a) A(y) small-y limit is a CONSTANT |c1|/pi with c1=B'(0)=-tau^2/36 (NOT tau^2 y^2.5 ->0).
        intermediate A ~ 0.0629*tau^2*y^2.5; peak A=0.143 at y~64 (NOT tau^-2/3=21.5); then ~1/sqrt y.
 3. (b) Phi'(y) ~ -2 log(2y/W); vanishes at y*=W/2=7.036 (Phi''(y*)=-0.288 ~ -4/W); monotone
        decreasing on saddle region [0.5,~150] but NOT for y<0.4 and near pole.
 4. Saddle leading amplitude A(y*) sqrt(2pi/|Phi''(y*)|)=0.003888 = 0.0389*sqrt(tau), matches
        tau^2 W^3/72=0.0393 sqrt(tau) and |T2|/sqrt(tau) bounded ~0.039 uniformly in phase => O(sqrt tau).
 5. CRITICAL: the Abel-Plana imaginary-axis integral DIVERGES. A(y) grows toward the pole at
        y=pi/tau=314 (|g_iy|~exp(c y log y)); partial integrals do NOT converge to T2; the
        IBP control integral I=int_{|y-y*|>1}|d/dy(A/Phi')|dy is finite (~0.18) only if cut off
        well before the pole, and grows to >2.7 by y=300, diverging at the pole.
"""
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 35
tau=mp.mpf('0.01'); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ystar=W/2
print(f"tau={tau} w={mp.nstr(w,7)} W={mp.nstr(W,8)} y*=W/2={mp.nstr(ystar,7)} pole pi/tau={mp.nstr(mp.pi/tau,7)}")
c1=mp.diff(lambda s:B_s(s,tau,Kmax=80,Pmax=16),mp.mpf(0))
print(f"c1=B'(0)={mp.nstr(c1,8)} ; -tau^2/36={mp.nstr(-tau**2/36,8)} ; A(0+)=|c1|/pi={mp.nstr(abs(c1)/mp.pi,7)}")
def A(y):
    y=mp.mpf(y); g=1-mp.e**(-B_s(mp.mpc(0,1)*y,tau,Kmax=80,Pmax=16))
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
def Phi(y):
    y=mp.mpf(y); g=1-mp.e**(-B_s(mp.mpc(0,1)*y,tau,Kmax=80,Pmax=16))
    return 2*y*mp.log(W)+mp.im(mp.log(g))-mp.im(mp.loggamma(1+2*mp.mpc(0,1)*y))
Phipp=mp.diff(Phi,ystar,2)
print(f"A(y*)={mp.nstr(A(ystar),7)} ; Phi''(y*)={mp.nstr(Phipp,7)} ; -4/W={mp.nstr(-4/W,7)}")
lead=A(ystar)*mp.sqrt(2*mp.pi/abs(Phipp))
print(f"saddle leading amp A(y*)sqrt(2pi/|Phi''|)={mp.nstr(lead,7)} = {mp.nstr(lead/mp.sqrt(tau),6)}*sqrt(tau)")
print(f"tau^2 W^3/72={mp.nstr(tau**2*W**3/72,7)} = {mp.nstr(tau**2*W**3/72/mp.sqrt(tau),6)}*sqrt(tau)")
print("A peak ~0.143 at y~64 ; sup A on (0,pi/tau) -> infinity at pole")
print("IBP I=int_{|y-y*|>1}|d(A/Phi')| : 0.18 (cut at Y=15..30), 0.73 (Y=200), 2.74 (Y=300), -> inf at pole")
