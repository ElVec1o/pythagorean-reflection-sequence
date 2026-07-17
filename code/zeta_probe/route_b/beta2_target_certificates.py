#!/usr/bin/env python3
"""v2.12.10: closure of the modular-parametrization hypothesis + certified anatomy of the
target number q* itself.

(1) MODULAR PARAMETRIZATION CLOSED (the one gap the ADE sweep could not cover, since
elimination from "algebraic over Q(j)" blows the degree past swept ADE profiles):
neither u_1 = z_1(q) nor S(q) is algebraic over Q(j) or over Q(t_2) (level-2 Hauptmodul
t_2 = (eta(q)/eta(q^2))^24) at bidegrees up to (40,40) [+ slack variant (20,20,+3)] --
constant-coefficient rank tests on 2000 coefficients mod p, all full rank = proofs per
profile. Sanity: J = q*j series matches 1,744,196884,21493760 mod p; T2 matches
1,-24,276,-2048,11202. Combined with v2.12.8's quasi-modular theta-log closure: NO
modular structure of any tested kind underlies the zero curve or the diagonal.

(2) TARGET CERTIFICATES (q* to 430 digits, Newton residual 1e-442, saved qstar_430.txt):
neither q* nor beta_2 = 1/sqrt(q*) satisfies an integer polynomial of degree <= 8 at
height 1e20, degree <= 12 at 1e18, degree <= 16 at 1e14 (PSLQ with post-verification of
every candidate at 1e-350; none appeared). No bilinear relation between q* and the fold
constant q_c (1e12, 200 digits).

(3) CONTINUED FRACTION OF q* (first examination; 383 certified partial quotients via
two-precision guard; data in qstar_cf.txt): Gauss-Kuzmin generic. Digit frequencies
match GK within noise; Khinchin geometric mean 2.6252 (limit 2.6854); Levy exponent
3.2064 (limit 3.2758); largest quotient a_170 = 8250, p ~ 6% over 383 draws --
unremarkable. No periodicity (consistent with the degree-16 exclusion), no pattern,
no near-rational anomaly. q* is CF-generic: the target looks like a generic
transcendental and offers no arithmetic foothold of any tested kind.
"""
import numpy as np, time
N=2000; p=46337
u1=np.load(f"u1_mod{p}.npy")
def mul(a,b): return (np.convolve(a,b)[:N+1]%p).astype(np.int64)
def inv_unit(a):
    x=np.zeros(N+1,dtype=np.int64); x[0]=pow(int(a[0]),p-2,p); k=1
    while k<=N:
        k2=min(2*k,N+1)
        ax=np.convolve(a[:k2],x[:k2])[:k2]%p
        t=(-ax)%p; t[0]=(t[0]+2)%p
        x[:k2]=np.convolve(x[:k2],t)[:k2]%p; k=k2
    return x
def etaq(step):
    """(q^step;q^step)_oo via pentagonal numbers"""
    c=np.zeros(N+1,dtype=np.int64); c[0]=1
    k=1
    while True:
        e1=step*k*(3*k-1)//2; e2=step*k*(3*k+1)//2
        if e1>N and e2>N: break
        s=1 if k%2==0 else -1
        if e1<=N: c[e1]=(c[e1]+s)%p
        if e2<=N: c[e2]=(c[e2]+s)%p
        k+=1
    return c
E=etaq(1); E2q=etaq(2)
def powmod_series(a,n):
    r=np.zeros(N+1,dtype=np.int64); r[0]=1
    b=a.copy()
    while n:
        if n&1: r=mul(r,b)
        b=mul(b,b); n>>=1
    return r
E24=powmod_series(E,24)
def E4():
    c=np.zeros(N+1,dtype=np.int64); c[0]=1
    sig=np.zeros(N+1,dtype=np.int64)
    for d in range(1,N+1):
        dd=pow(d,3,p)
        for m in range(d,N+1,d): sig[m]=(sig[m]+dd)%p
    c[1:]=240*sig[1:]%p; return c
# J := q*j(q) = E4^3 / (q;q)oo^24  (Delta = q*(q;q)oo^24; q*j = q*E4^3/Delta = E4^3/(q;q)oo^24)
J=mul(powmod_series(E4(),3),inv_unit(E24))
print("J = q*j sanity (expect 1, 744, 196884, 21493760):",[int(x) for x in J[:4]])
# T2 := q*t2 where t2 = (eta(q)/eta(q^2))^24 = q^{-1} ((q;q)oo/(q^2;q^2)oo)^24
T2=mul(powmod_series(E,24),inv_unit(powmod_series(E2q,24)))
print("T2 = q*t2 first coeffs:",[int(x if x<p//2 else x-p) for x in T2[:5]])
def rank_modp(cols):
    A=np.stack(cols,axis=1)%p; R,C=A.shape; r=0
    for c in range(C):
        piv=np.nonzero(A[r:,c])[0]
        if piv.size==0: continue
        pr=r+piv[0]
        if pr!=r: A[[r,pr]]=A[[pr,r]]
        A[r,c:]=A[r,c:]*pow(int(A[r,c]),p-2,p)%p
        f=A[r+1:,c]; nz=np.nonzero(f)[0]
        if nz.size: A[r+1+nz,c:]=(A[r+1+nz,c:]-np.outer(f[nz],A[r,c:]))%p
        r+=1
        if r==R: break
    return r,C
t0=time.time()
def algtest(name,Xser,Wser,dU,dW,slack):
    """P(X, W/q) = 0, constant coeffs: columns X^a W^b q^{(dW-b)+e}, e<=slack"""
    XP=[np.zeros(N+1,dtype=np.int64) for _ in range(dU+1)]; XP[0][0]=1
    for a in range(1,dU+1): XP[a]=mul(XP[a-1],Xser)
    WP=[np.zeros(N+1,dtype=np.int64) for _ in range(dW+1)]; WP[0][0]=1
    for b in range(1,dW+1): WP[b]=mul(WP[b-1],Wser)
    cols=[]
    for a in range(dU+1):
        for b in range(dW+1):
            base=mul(XP[a],WP[b])
            for e in range(slack+1):
                c=np.zeros(N+1,dtype=np.int64)
                sh=(dW-b)+e
                c[sh:]=base[:N+1-sh]
                cols.append(c)
    r,C=rank_modp(cols)
    print(f"  {name} bideg ({dU},{dW}) slack {slack}: {C} unknowns, rank {r} -> {'!!! KERNEL '+str(C-r) if r<C else 'none'}  [{time.time()-t0:.0f}s]")
print("u1 algebraic over Q(j)?")
algtest("j",u1,J,40,40,0)
algtest("j",u1,J,20,20,3)
print("u1 algebraic over Q(t2) (level-2 Hauptmodul)?")
algtest("t2",u1,T2,40,40,0)
algtest("t2",u1,T2,20,20,3)
print("S algebraic over Q(j), Q(t2)?")
S=np.load("S_mod46337.npy")
algtest("j",S,J,40,40,0)
algtest("t2",S,T2,40,40,0)
# ===== q* 430 digits + PSLQ + continued fraction =====
from mpmath import mp, mpf, pslq, sqrt
mp.dps=440
def S(q):
    w=2*q*(1-q)
    tot=mp.mpf(1); term=mp.mpf(1)
    for k in range(1,60):
        term*=-q**(2*(k-1))*w/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
    return tot
# Newton with numeric derivative
q=mpf('0.4493688577880881108')
h=mpf(10)**-200
for it in range(12):
    f=S(q)
    df=(S(q+h)-S(q-h))/(2*h)
    q-=f/df
print("q* residual:",mp.nstr(abs(S(q)),3))
print("q* =",mp.nstr(q,60),"...")
with open("qstar_430.txt","w") as f: f.write(mp.nstr(q,432))
beta2=1/sqrt(q)
print("beta2 =",mp.nstr(beta2,40),"...")
mp.dps=430
# PSLQ: certified windows. precision budget: (deg+1)*log10(H) << 400
print()
for name,x in [("q*",q),("beta2",beta2)]:
    for (deg,H,tol) in [(8,10**20,mpf(10)**-380),(12,10**18,mpf(10)**-380),(16,10**14,mpf(10)**-380)]:
        r=pslq([x**i for i in range(deg+1)],tol=tol,maxcoeff=H,maxsteps=3*10**6)
        if r:
            # certify: evaluate
            v=sum(r[i]*x**i for i in range(deg+1))
            verdict="GENUINE" if abs(v)<mpf(10)**-350 else f"SPURIOUS (res {mp.nstr(abs(v),3)})"
            print(f"  {name} deg {deg} H=1e{len(str(H))-1}: relation {r} -> {verdict}")
        else:
            print(f"  {name} deg {deg} H=1e{len(str(H))-1}: none -- CERTIFIED")
# joint with fold constants? q* vs q_c: any rational relation? quick basket
qc=mpf(open("fold_coords_230.txt").readline().strip())
mp.dps=200
r=pslq([mpf(1),q,qc,q*qc,q*q,qc*qc],tol=mpf(10)**-180,maxcoeff=10**12,maxsteps=10**6)
print("  joint (q*, q_c) bilinear:",r if r else "none (height 1e12, 200dg)")
from mpmath import mp, mpf
import math
qs=open("qstar_430.txt").read().strip()
def cf(digits):
    mp.dps=len(digits)-2
    x=mpf(digits)
    out=[]
    for _ in range(1000):
        a=int(mp.floor(x)); out.append(a)
        fr=x-a
        if fr<mpf(10)**-(mp.dps-8): break
        x=1/fr
    return out
full=cf(qs)
trunc=cf(qs[:390])
n=0
while n<min(len(full),len(trunc)) and full[n]==trunc[n]: n+=1
pq=full[:n]
print(f"reliable partial quotients: {n}")
print("q* = [0;",",".join(str(x) for x in pq[1:61]),",...]")
mx=max(pq[1:]); mxi=pq.index(mx)
print(f"largest partial quotient: a_{mxi} = {mx}")
big=[(i,a) for i,a in enumerate(pq[1:],1) if a>=50]
print("quotients >= 50:",big)
# Gauss-Kuzmin: P(a=k) = log2(1+1/(k(k+2)))
from collections import Counter
c=Counter(pq[1:])
tot=len(pq)-1
print("\n a | observed | Gauss-Kuzmin")
for k in range(1,9):
    gk=math.log2(1+1/(k*(k+2)))
    print(f" {k} | {c[k]/tot:.4f}   | {gk:.4f}")
# Khinchin: geometric mean -> 2.6854
gm=math.exp(sum(math.log(a) for a in pq[1:])/tot)
print(f"\ngeometric mean of a_k: {gm:.4f}  (Khinchin 2.6854)")
# Levy: q_n^{1/n} -> e^{pi^2/(12 ln 2)} = 3.2758
Pn,Qn=0,1; Pm,Qm=1,0
import fractions
for a in pq[1:]:
    Pn,Pm=a*Pn+Pm,Pn; Qn,Qm=a*Qn+Qm,Qn
lev=Qn**(1.0/(tot)) if Qn<10**300 else math.exp(math.log(Qn)/tot)
print(f"Levy constant estimate: {math.exp(math.log(Qn)/tot):.4f}  (Levy 3.2758)")
with open("/Users/vico/Documents/elvec1o/certify_run/code/zeta_probe/route_b/qstar_cf.txt","w") as f:
    f.write("q* partial quotients (reliable prefix, two-precision guard, 430 digits)\n")
    f.write(",".join(str(x) for x in pq))
print("\nsaved to repo: qstar_cf.txt")
