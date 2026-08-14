"""
GAP-V rigorous inputs for the lem:T2abs writeup.
(1) |B_s| <= C sqrt(tau) on the strip S={Re s in[1/2,..], 0<=Im s<=W/2} (and its closure) -- report sup C.
    The amplitude bound |g_s|=|1-e^{-B_s}| <= |B_s| e^{|B_s|} then gives |g_s| <= C' sqrt(tau).
(2) Confirm per-edge: top O(sqrt tau) const, left O(sqrt tau log) -- already have; here re-confirm sup C
    is attained near the diagonal corner s=(W/2)(1+i) [where |B_s|~sqrt(tau)], NOT on Re s=1/2.
(3) A >= |T2| sanity with a CLEAN T2 (Abel-Plana T2 from the cocycle, no S1_bulk garbage).
Scalar mpmath, dps=30, fast: sup over a modest grid on S; few tau.
"""
import mpmath as mp
from abelplana_verify import B_exact
mp.mp.dps = 30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def Bval(s,tau):
    v,_=B_exact(s,tau); return v

print("(1) sup_{S} |B_s|/sqrt(tau) and argmax  (grid over Re s in[1/2,W], Im s in[0,W/2]):")
print(f"{'tau':>9}{'W':>8}{'sup|B|/st':>11}{'argRe/W':>9}{'argIm/W':>9}{'|g|/st@max':>11}")
Cs=[]
for taus in ['0.05','0.02','0.01','0.005','0.002','0.001']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    best=mp.mpf(0); ar=ai=mp.mpf(0); bg=mp.mpf(0)
    NR=14; NI=14
    for i in range(NR+1):
        sig=mp.mpf('0.5')+(W-mp.mpf('0.5'))*i/NR
        for j in range(NI+1):
            t=(W/2)*j/NI
            s=mp.mpc(sig,float(t)); B=Bval(s,tau); ab=abs(B)
            if ab>best:
                best=ab; ar=sig; ai=t; bg=abs(1-mp.e**(-B))
    Cs.append(float(best/st))
    print(f"{taus:>9}{float(W):>8.2f}{float(best/st):>11.4f}{float(ar/W):>9.3f}{float(ai/W):>9.3f}{float(bg/st):>11.4f}")
print(f"   => C := sup |B_s|/sqrt(tau) ~ {max(Cs):.4f} (use C=0.20, C'=C e^{{C sqrt tau}} ~0.20 for small tau)")

print("\n(2) |B_s|/sqrt(tau) ON the left edge Re s=1/2 (should be SMALLER -- left edge amplitude is mild):")
print(f"{'tau':>9}{'maxleft|B|/st':>14}{'@Im/W':>8}")
for taus in ['0.02','0.005','0.001']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    best=mp.mpf(0); aj=mp.mpf(0)
    for j in range(41):
        t=(W/2)*j/40; s=mp.mpc('0.5',float(t)); ab=abs(Bval(s,tau))
        if ab>best: best=ab; aj=t
    print(f"{taus:>9}{float(best/st):>14.4f}{float(aj/W):>8.3f}")

print("\n(3) A >= |T2| with CLEAN T2 from the cocycle (P12-block identity), dps=30:")
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x
def S1bulk_clean(q):
    # S1 = 1 - P22(=Se) ... use the cocycle bulk: 1 - Se? No -- S1_bulk = 1 - prod? Use direct alpha/gamma but high N.
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(60000):
        a=2*q**(2*j+2)/(1-q**(2*j+2)); g=2*q**(2*j+3)/(1-q**(2*j+3))-2*q**(2*j+2)/(1-q**(2*j+2))
        tot+=a*prod; prod*=g
        if abs(prod)<mp.mpf(10)**(-40) and j>80: break
    return tot
for taus in ['0.05','0.02','0.01']:
    tau=mp.mpf(taus); q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    S1=S1bulk_clean(q)
    T2=S1-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
    print(f"   tau={taus} |T2|/sqrt(tau)={float(abs(T2)/mp.sqrt(tau)):.5f}")
