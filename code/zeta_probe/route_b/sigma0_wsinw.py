#!/usr/bin/env python3
"""
Confirm the FUNCTIONAL asymptotic  Sigma_0(q) ~ w sin w  (w=sqrt(2/tau), tau=-ln q) as q->1,
OFF the poles, at high precision -- the companion to lem:cos (Sigma_1 ~ 1-cos w).
Note w sin w = 2*theta(1-cos w), theta=(1/2) w d/dw.  Also test S_0^bulk ~ w sin w likewise.
If Sigma_0(q) = w sin w + o(w), then at poles w_m=(m-1/2)pi: Sigma_0(q_m) ~ (-1)^{m+1} w_m,
|.|->inf, ALTERNATING => no zeros for large m => V-numerator non-vanishing is a THEOREM.
"""
import mpmath as mp
mp.mp.dps=120

def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=20000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>60: break
    return tot

print("Off-pole functional asymptotic Sigma_0(q) vs w sin w, and ratio -> 1:")
print(f"{'tau':>10} {'w':>12} {'Sigma_0':>16} {'w sin w':>16} {'ratio':>12} {'(S0-wsinw)/w':>14}")
for tau in [mp.mpf('0.05'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002'),mp.mpf('0.001'),mp.mpf('0.0005'),mp.mpf('0.0002')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    s0=Sig(0,q); ws=w*mp.sin(w)
    print(f"{mp.nstr(tau,4):>10} {mp.nstr(w,8):>12} {mp.nstr(s0,10):>16} {mp.nstr(ws,10):>16} {mp.nstr(s0/ws,9):>12} {mp.nstr((s0-ws)/w,8):>14}")

print("\nSame for bulk numerator S_0^bulk(q) vs w sin w:")
print(f"{'tau':>10} {'w':>12} {'S0_bulk':>16} {'w sin w':>16} {'ratio':>12}")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002'),mp.mpf('0.001'),mp.mpf('0.0005')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    sb0=Sb(0,q); ws=w*mp.sin(w)
    print(f"{mp.nstr(tau,4):>10} {mp.nstr(w,8):>12} {mp.nstr(sb0,10):>16} {mp.nstr(ws,10):>16} {mp.nstr(sb0/ws,9):>12}")

print("\nEngine check: is Sigma_0 ~ 2*theta(1-cos w)=w sin w AND Sigma_1 ~ 1-cos w consistent?")
for tau in [mp.mpf('0.01'),mp.mpf('0.002'),mp.mpf('0.0005')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    s1=Sig(1,q); s0=Sig(0,q)
    print(f"  tau={mp.nstr(tau,3)}: Sigma_1={mp.nstr(s1,8)} vs 1-cos w={mp.nstr(1-mp.cos(w),8)}; "
          f"Sigma_0/(w sin w)={mp.nstr(s0/(w*mp.sin(w)),8)}")
