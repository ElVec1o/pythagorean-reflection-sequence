"""
Measure the deviation of S_1 from its limit at the two extreme phase families:
  family E (even): w=2n*pi  -> claim S1 -> 0.   measure d0(n)=S1.
  family O (odd):  w=(2n+1)pi -> claim S1 -> 2. measure d2(n)=2-S1.
Fit decay rate in n (and in tau=2/w^2). This pins the 'remaining lemma' precisely.
Fast: forward recursion; dps auto.
"""
import mpmath as mp, math
def alpha(k,tau): return 2/(mp.e**((k+1)*tau)-1)
def S1c(tau,dps):
    mp.mp.dps=dps
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(3000000):
        tot+=alpha(1+2*j,tau)*prod
        prod*=(alpha(2+2*j,tau)-alpha(1+2*j,tau))
        if abs(prod)<mp.mpf(10)**(-(dps-15)) and j>40: break
    return tot

print("EVEN family w=2n*pi (limit 0):    ODD family w=(2n+1)pi (limit 2):")
print("  n     S1(even)=d0      d0*n      d0/tau      2-S1(odd)=d2    d2*n     d2/tau")
for n in [4,8,16,32,64,128]:
    we=2*n*mp.pi; te=2/we**2; dpse=int(float(we)/math.log(10))+50
    s_e=S1c(te,dpse); d0=s_e
    wo=(2*n+1)*mp.pi; to=2/wo**2; dpso=int(float(wo)/math.log(10))+50
    s_o=S1c(to,dpso); d2=2-s_o
    print(f"  {n:4d}  {mp.nstr(d0,7):>12s} {mp.nstr(d0*n,6):>9s} {mp.nstr(d0/te,6):>10s}    {mp.nstr(d2,7):>12s} {mp.nstr(d2*n,6):>8s} {mp.nstr(d2/to,6)}")
