#!/usr/bin/env python3
"""
DERIVE Sigma_0 ~ w sin w by the SAME layer machinery as lem:cos (Sigma_1 ~ 1-cos w).

Recursion (travel; bulk identical with alpha,gamma):
  Sigma_k = sum_{j>=0} (-1)^? * (term_j),  term_j = A_{start+2j} * prod_{i<j} C_{start+2i}
  S_1/Sigma_1: start=1 (ODD ladder).   S_0/Sigma_0: start=0 (EVEN ladder).
Leading model as tau->0 (A_k ~ 2/((k+1)tau)*g, g=y/(e^y-1)<=1; C_k ~ -2/(tau(k+1)(k+2))):
  odd  ladder term_j ~ (-1)^j (2/tau)^{j+1}/(2j+2)!   => sum = 1 - cos w      [KNOWN]
  even ladder term_j ~ (-1)^j (2/tau)^{j+1}/(2j+1)!   => sum = w sin w        [CLAIM]
because prod_{i<j} of denominators differs by one index-parity shift: (2j+2)! <-> (2j+1)!.
Also hat s_j / hat t_j = (2j+2)!/(2j+1)! = (2j+2) = the amplitude factor turning
1-cos w into w sin w (w sin w = sum (-1)^{m-1}(2m) w^{2m}/(2m)!).

TESTS:
 (1) sum_j (-1)^j (2/tau)^{j+1}/(2j+1)! == w sin w  (exact identity).
 (2) the ACTUAL even-ladder terms s_j (from alpha,gamma) have s_j/hat s_j = sigma_j in (0,1],
     decreasing to 0  (lem:dom analog).
 (3) S_0 = sum_j (-1)^j s_j  reproduces Sb(0,q)  (consistency of the layer sum).
 (4) S_0 = w sin w + bounded correction; at sin w=+-1 the correction stays O(1).
"""
import mpmath as mp
mp.mp.dps=50

def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=4000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>40: break
    return tot

# (1) exact identity sum_j (-1)^j (w^2)^{j+1}/(2j+1)! = w sin w
print("(1) identity sum_j (-1)^j (w^2)^{j+1}/(2j+1)! =? w sin w")
for w in [mp.mpf(3),mp.mpf(10),mp.mpf(25)]:
    S=mp.nsum(lambda j: (-1)**int(j)*(w**2)**(j+1)/mp.factorial(2*j+1), [0,mp.inf])
    print(f"   w={mp.nstr(w,4)}: sum={mp.nstr(S,12)}  w sin w={mp.nstr(w*mp.sin(w),12)}  match={abs(S-w*mp.sin(w))<mp.mpf(10)**(-20)}")

# (2)+(3): actual layer terms, sigma_j, and layer-sum vs Sb(0,.)
print("\n(2)/(3) even-ladder layers at tau=0.01 (w=14.14):")
tau=mp.mpf('0.01'); q=mp.e**(-tau); w=mp.sqrt(2/tau)
def layers(start,q,J=200):
    out=[]; prod=mp.mpf(1)
    for j in range(J):
        term=alpha(start+2*j,q)*prod   # the j-th additive term of Sb(start,.)
        out.append(term); prod*=gamma(start+2*j,q)
        if abs(prod)<mp.mpf(10)**(-60) and j>40: break
    return out
L0=layers(0,q)
S0_layersum=sum(L0)
hat=lambda j: (2/tau)**(j+1)/mp.factorial(2*j+1)
print(f"   S_0 via layer sum = {mp.nstr(S0_layersum,12)},  Sb(0,q) = {mp.nstr(Sb(0,q),12)},  match={abs(S0_layersum-Sb(0,q))<mp.mpf(10)**(-12)}")
print(f"   sigma_j = s_j/hat s_j for j=0..10 (should be in (0,1], decreasing):")
sig=[abs(L0[j])/hat(j) for j in range(min(11,len(L0)))]
print("   ", [mp.nstr(s,7) for s in sig])
print("   in (0,1]:", all(0<s<=1+mp.mpf('1e-9') for s in sig), " decreasing:", all(sig[i]>=sig[i+1]-mp.mpf('1e-9') for i in range(len(sig)-1)))

# (4) S_0 vs w sin w + correction at several tau (off pole), and the bounded correction
print("\n(4) S_0(q) - w sin w  (the correction), vs w, across tau:")
print(f"{'tau':>9} {'w':>9} {'S0':>14} {'w sin w':>14} {'S0 - w sinw':>13}")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.004'),mp.mpf('0.001')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau); s0=Sb(0,q); ws=w*mp.sin(w)
    print(f"{mp.nstr(tau,3):>9} {mp.nstr(w,6):>9} {mp.nstr(s0,9):>14} {mp.nstr(ws,9):>14} {mp.nstr(s0-ws,7):>13}")
