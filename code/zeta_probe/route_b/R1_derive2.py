import mpmath as mp
mp.mp.dps=150   # high dps so Sb sums stay accurate to high m
def gamma_b(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def alpha_b(k,q): return 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=200000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha_b(k+2*j,q)*prod; prod*=gamma_b(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-300) and j>60: break
    return tot
# travel block for pole sanity
def At(k,q): return 2*q/(1-q**(k+1))
def Ct(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=200000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=At(k+2*j,q)*prod; prod*=Ct(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-300) and j>60: break
    return tot
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*100)
print("R1 ANALYTIC DECOMPOSITION at travel poles (high dps):")
print(" Se=1-S1b ~ 1/w,  So ~ 1/w,  So-Se=O(tau).  => So/Se = 1+O(sqrt tau) -> 1.")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'Sig1res':>9} {'w*Se':>11} {'w*So':>11} {'(So-Se)*w':>12} {'So/Se':>13}")
for m in [2,4,8,16,32,48,64,80]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    sigres=Sig(1,q)-1
    s0b=Sb(0,q); s1b=Sb(1,q); Se=1-s1b; So=(1-q)/(2*q)*s0b
    print(f"{m:>3} {float(tau):>10.6f} {float(sigres):>9.1e} {float(w*Se):>11.7f} {float(w*So):>11.7f} {float((So-Se)*w):>12.3e} {float(So/Se):>13.9f}")
print()
print("w*Se -> ? and w*So -> ? (both -> sqrt(2)*1/2*? ). Check limit constant:")
print("Recall Se=1-S1b ~ cos w * 18 ; cos w_m ~ (sqrt2/36) sqrt(tau); so Se ~ 18*(sqrt2/36)*sqrt(tau)")
print("     = (sqrt2/2) sqrt(tau) = sqrt(tau/2) = 1/w.  So w*Se -> 1. Confirmed above.")
print()
# Now the cleaner identity: at the pole, cos(w_m) is FIXED by Sigma_1^travel=1. Verify the
# established lem:cos relation: cos(w_m)/sqrt(tau) -> sqrt2/36 (this is what makes Se~1/w).
print(f"{'m':>3} {'cos w_m/sqrt(tau)':>18} {'-> sqrt2/36=':>14}")
for m in [4,8,16,32,48,64,80]:
    if m>len(poles):break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    print(f"{m:>3} {float(mp.cos(w)/mp.sqrt(tau)):>18.9f} {float(mp.sqrt(2)/36):>14.9f}")
