#!/usr/bin/env python3
"""
DEDICATED SWING: steepest-descent proof strategy for lem:cos, verified numerically.

T_2 = G(iW),  G(z)=sum_{i>=1} g_i z^{2i}/(2i)!,  g_i=1-e^{-B_i},  W=w e^{-tau/2}.
Saddle of the alternating sum at s* = iW/2 (the subdominant/imaginary direction).
There g_{s*} ~ B_{s*}, and B_s ~ (tau^2/9) s^3 (leading) continues to s*:
   B_{s*} ~ (tau^2/9)(iW/2)^3 = -i tau^2 W^3/72 = O(sqrt tau)   [tau^2 W^3 = 2 sqrt2 sqrt tau]
PREDICTION:  T_2 = Re[ B_{s*} e^{iW} ] + (lower order) = (tau^2 W^3/72) sin W + ...
We test this against the TRUE T_2 = S_1 - (1-cos w) - T_1,  T_1 = cos w - cos W.
If it matches, the saddle MECHANISM (and hence the proof strategy) is correct.

Also test the convergence of the tau-series of B at the COMPLEX saddle (tau (W/2)^2 = 1/2 < radius).
"""
import mpmath as mp
mp.mp.dps=60

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb1(q,J=6000):  # BULK S_1
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(1+2*j,q)*prod; prod*=gamma(1+2*j,q)
        if abs(prod)<mp.mpf(10)**(-110) and j>50: break
    return tot

print("Saddle prediction  T_2 =? Re[B_{s*} e^{iW}],  B_{s*}=(tau^2/9)(iW/2)^3 = -i tau^2 W^3/72")
print(f"{'tau':>10} {'w':>9} {'T_2 (true)':>16} {'saddle Re[B* e^iW]':>20} {'ratio':>10}")
for tau in [mp.mpf('0.02'),mp.mpf('0.008'),mp.mpf('0.003'),mp.mpf('0.001'),mp.mpf('0.0004'),mp.mpf('0.00015')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    S1=Sb1(q)
    T1=mp.cos(w)-mp.cos(W)
    T2_true=S1-(1-mp.cos(w))-T1
    # saddle: B_{s*} = (tau^2/9)(i W/2)^3  (leading)
    sstar=mp.mpc(0,1)*W/2
    Bstar=(tau**2/9)*sstar**3
    saddle=mp.re(Bstar*mp.e**(mp.mpc(0,1)*W))
    print(f"{mp.nstr(tau,4):>10} {mp.nstr(w,6):>9} {mp.nstr(T2_true,9):>16} {mp.nstr(saddle,9):>20} {mp.nstr(T2_true/saddle,7):>10}")

print("\nUse FULL cubic C(s)=(s+1)(2s+3)(4s+5)/72 (the R-control majorant) at s*=iW/2 instead of s^3/9:")
print(f"{'tau':>10} {'T_2 (true)':>16} {'Re[tau^2 C(s*) e^iW]':>22} {'ratio':>10}")
for tau in [mp.mpf('0.008'),mp.mpf('0.001'),mp.mpf('0.00015')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    T2_true=Sb1(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
    sstar=mp.mpc(0,1)*W/2
    C=(sstar+1)*(2*sstar+3)*(4*sstar+5)/72
    pred=mp.re(tau**2*C*mp.e**(mp.mpc(0,1)*W))
    print(f"{mp.nstr(tau,4):>10} {mp.nstr(T2_true,9):>16} {mp.nstr(pred,9):>22} {mp.nstr(T2_true/pred,7):>10}")

print("\nConvergence of tau-series of B at the saddle: tau*(W/2)^2 =", end=" ")
tau=mp.mpf('0.001'); W=mp.sqrt(2/tau)*mp.e**(-tau/2)
print(mp.nstr(tau*(W/2)**2,6), "(< radius ~ (2pi)^2/2? the phi-series radius => series converges at s*)")
