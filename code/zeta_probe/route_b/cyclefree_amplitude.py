#!/usr/bin/env python3
"""
A_U > 0 via DOMINANT cycle-free amplitude.
  S_0 = sum_c N^{(c)} ~ w sin w  (amplitude A_total = 1, proven).
  N_U(q_m) ~ (sum_c q_m^c A_c) w sin w,  A_c = lead w-sin-w amplitude of the c-cycle numerator.
SUFFICIENT for N_U(q_m) != 0:  A_0 > sum_{c>=1}|A_c|.  Since sum_c A_c = 1, this holds if A_0 > 1/2
AND A_{c>=1} >= 0 (or more weakly A_0 > sum|A_c|).

A_0 = amplitude of the CYCLE-FREE (gapless) bulk block, which HAS a clean telescoping:
gapless = deposits on CONSECUTIVE edges (no gap edges => connected => c=0). Transfer over
sizes a,b>=1: P_b = 2q^b (1 + sum_a P_a q^{max(a,b)}),  B_0 = sum_b P_b.
We compute B_0(q), continue to q->1, and read A_0 = lim B_0/(w sin w). Compare to S_0 ~ +w sin w.
"""
import mpmath as mp
mp.mp.dps=40

def gapless_block(q, Smax=120):
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
    # P_b = 2q^b + sum_a 2q^b q^{max(a,b)} P_a  => (I - M) P = e, M[b,a]=2q^b q^{max(a,b)}, e_b=2q^b
    e=mp.matrix(n,1); M=mp.matrix(n,n)
    for b in sizes:
        e[idx[b],0]=2*q**b
        for a in sizes:
            M[idx[b],idx[a]]=2*q**b*q**max(a,b)
    P=mp.lu_solve(mp.eye(n)-M,e)
    return sum(P[i,0] for i in range(n))

# full relaxed bulk numerator S_0 (telescoped) for comparison
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=4000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>40: break
    return tot
def S0full(q): return Sb(0,q)        # = sum_c N^{(c)}, ~ w sin w
def S1(q): return Sb(1,q)

print("Is the gapless (cycle-free) block B_0 ~ A_0 w sin w, and is A_0 the DOMINANT share of S_0?")
print(f"{'tau':>9} {'w':>9} {'B_0(gapless)':>14} {'S_0(full)':>13} {'B_0/S_0':>10} {'B_0/(wsinw)':>13}")
for tau in [mp.mpf('0.05'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002'),mp.mpf('0.001')]:
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    B0=gapless_block(q); S0=S0full(q); ws=w*mp.sin(w)
    print(f"{mp.nstr(tau,3):>9} {mp.nstr(w,6):>9} {mp.nstr(B0,8):>14} {mp.nstr(S0,8):>13} {mp.nstr(B0/S0,7):>10} {mp.nstr(B0/ws,8):>13}")

print()
print("At the TRAVEL poles (S1=1), cycle-free share B_0(q_m)/S_0(q_m):")
def bisect(f,a,b,it=200):
    fa=f(a)
    for _ in range(it):
        m=(a+b)/2
        if mp.sign(f(m))==mp.sign(fa): a=m
        else: b=m
    return (a+b)/2
roots=[]; w=mp.mpf('2.0'); prev=None; pv=None
while len(roots)<8 and w<40:
    q=mp.e**(-2/w**2); val=S1(q)-1
    if prev is not None and mp.sign(val)!=mp.sign(prev):
        r=bisect(lambda qq:S1(qq)-1,pv,q); roots.append(r)
    prev=val; pv=q; w+=mp.mpf('0.05')
print(f"{'q_m':>14} {'B_0(q_m)':>12} {'S_0(q_m)':>12} {'share B_0/S_0':>13}")
for r in roots:
    B0=gapless_block(r); S0=S0full(r)
    print(f"{mp.nstr(r,10):>14} {mp.nstr(B0,7):>12} {mp.nstr(S0,7):>12} {mp.nstr(B0/S0,6):>13}")
