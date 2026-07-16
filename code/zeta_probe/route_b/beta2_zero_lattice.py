#!/usr/bin/env python3
"""v2.12.5: THE INTEGRAL ZERO LATTICE + the Mahler no-go battery on the zero curve.

THEOREM (companion thm:integrality, upgraded): for EVERY k>=1, u_k := q^{2(k-1)} z_k(q)
lies in 1 + q Z[[q]].  Proof: q^{k(k-1)} G(q, u q^{-2(k-1)}) =
sum_{k'} (-1)^{k'} q^{(k'-k)(k'-k+1)} u^{k'} / (q;q)_{2k'}   [exponent identity],
the exponent is >=0 vanishing exactly at k' in {k-1,k} (strictly convex Newton polygon,
one zero per edge), F_k(0,u) = (-1)^{k-1} u^{k-1}(1-u), Hensel at u=1 with unit derivative.
MEASURED (order 300, k<=4): u_k - 1 first appears at order k(2k-1) (hexagonal numbers):
u_2 = 1 - q^6 - 2q^8 + q^9 - ..., u_3 = 1 - q^15 - ..., u_4 = 1 - q^28 - ...
Odd parts delayed: first odd coefficients at q^1, q^9, q^15, q^35.

AGGREGATE MAHLER IDENTITY (proved, one line from the zero product at bases q, -q, q^2,
using (q;q^2)oo(-q;q^2)oo = (q^2;q^4)oo):   prod_k phi_k = 1,
phi_k := u_k(q)u_k(-q)/u_k(q^2).  NOT termwise: phi_1 = 1+2q^6+4q^8+8q^10+18q^12+...,
phi_2 = 1-2q^6-..., phi_3 = 1+2q^20+..., phi_4 = 1-2q^28-... (adjacent defects cancel
in pairs; prod_{k<=4} = 1 + O(q^54)).

MAHLER NO-GO (measured, all full column rank on 300 exact integer coefficients):
 - no P(q, u1(q), u1(q^d)) = 0, d = 2,3, bidegrees (24,2,2), (16,3,3), (10,4,4);
 - no bilinear-profile system relation among {u1,u2,u3} at base q and u1 at q^2;
 - no zero of the base-q^2 cosine/sine equal to q^e * rational * z_i(q)^a w_j(q)^b,
   |e|<=10, a+b<=2 (60-digit hunt, cross-checked at q = 0.3 and 0.37);
 - phi_1 is not a log-linear combination of {log u_k(q^2), log u_k(q)u_k(-q): k=2,3,4}.
CONSEQUENCE: Mahler's method -- the one engine with no classical shadow, hence not blocked
by the step-ratio law -- has no visible foothold on the zero curve either.  Extends the
S-side no-Mahler theorem (mahler-route-killed) to the curve, empirically.

OPS NOTE: integer Newton needs inv_unit with leading coefficient +-1 (F'_k(0,1) = (-1)^k).
"""
import json
M=300
def mul(a,b):
    c=[0]*(M+1)
    for i,ai in enumerate(a):
        if ai==0: continue
        for j in range(M+1-i):
            if b[j]: c[i+j]+=ai*b[j]
    return c
def add(a,b): return [x+y for x,y in zip(a,b)]
def sub(a,b): return [x-y for x,y in zip(a,b)]
def inv_unit(a):
    u=a[0]; assert u in (1,-1)
    c=[0]*(M+1); c[0]=u
    for n in range(1,M+1): c[n]=-u*sum(a[i]*c[n-i] for i in range(1,n+1) if a[i])
    return c
def qpow(n):
    c=[0]*(M+1)
    if n<=M: c[n]=1
    return c
ONE=qpow(0)
IP={}
def inv_poch(m):
    if m in IP: return IP[m]
    c=[0]*(M+1); c[0]=1
    for part in range(1,m+1):
        for n in range(part,M+1): c[n]+=c[n-part]
    IP[m]=c; return c
def u_branch(k):
    """u_k: Hensel branch of F_k(q,u) = sum_{k'} (-1)^{k'} q^{(k'-k)(k'-k+1)} u^{k'}/(q;q)_{2k'}"""
    terms=[]
    for kp in range(0, k+20):
        e=(kp-k)*(kp-k+1)
        if e>M: 
            if kp>k: break
            else: continue
        terms.append((kp, [(-1)**kp * x for x in mul(qpow(e), inv_poch(2*kp))]))
    def F(u):
        tot=[0]*(M+1); up={0:ONE[:]}
        mx=max(kp for kp,_ in terms)
        cur=ONE[:]
        pows=[cur]
        for i in range(mx): cur=mul(cur,u); pows.append(cur)
        for kp,cf in terms: tot=add(tot,mul(cf,pows[kp]))
        return tot
    def Fu(u):
        tot=[0]*(M+1)
        mx=max(kp for kp,_ in terms)
        cur=ONE[:]; pows=[cur]
        for i in range(mx): cur=mul(cur,u); pows.append(cur)
        for kp,cf in terms:
            if kp>=1: tot=add(tot,[kp*x for x in mul(cf,pows[kp-1])])
        return tot
    u=ONE[:]
    for _ in range(10): u=sub(u,mul(F(u),inv_unit(Fu(u))))
    assert all(x==0 for x in F(u)), f"residual nonzero k={k}"
    return u
us={}
for k in (1,2,3,4):
    us[k]=u_branch(k)
    print(f"u_{k}: integral, u_{k}(0)={us[k][0]}, first coeffs {us[k][:8]}")
json.dump(us[1],open("u1_300.json","w"))
json.dump({str(k):us[k] for k in us},open("ulattice_300.json","w"))
# sanity: u1 must match previous z1 (order 120)
z1_old=json.load(open("/tmp/z1_120.json"))
print("u1 == old z1 through 120:", us[1][:121]==z1_old)
# phi_k = u_k(q)u_k(-q)/u_k(q^2): leading structure + aggregate check
def negq(a): return [((-1)**n)*a[n] for n in range(M+1)]
def sq(a):
    c=[0]*(M+1)
    for n in range(M+1):
        if 2*n<=M: c[2*n]=a[n]
    return c
phis={}
agg=ONE[:]
for k in (1,2,3,4):
    ph=mul(mul(us[k],negq(us[k])),inv_unit(sq(us[k])))
    phis[k]=ph
    nz=[n for n in range(1,M+1) if ph[n]!=0]
    print(f"phi_{k} = 1 + {ph[nz[0]]}*q^{nz[0]} + ...  (first nonzero at {nz[0]})" if nz else f"phi_{k} = 1 EXACTLY")
    agg=mul(agg,ph)
nz=[n for n in range(1,M+1) if agg[n]!=0]
print("aggregate prod_{k<=4} phi_k = 1 + O(q^%s)"%(nz[0] if nz else ">300"))
# ===== search battery (parity, log-identification, Mahler single + system) =====
from fractions import Fraction as Fr
us={int(k):v for k,v in json.load(open("ulattice_300.json")).items()}
M=300
def mul(a,b):
    c=[0]*(M+1)
    for i,ai in enumerate(a):
        if ai==0: continue
        for j in range(M+1-i):
            if b[j]: c[i+j]+=ai*b[j]
    return c
def inv_unit(a):
    u=a[0]; c=[0]*(M+1); c[0]=u
    for n in range(1,M+1): c[n]=-u*sum(a[i]*c[n-i] for i in range(1,n+1) if a[i])
    return c
def negq(a): return [((-1)**n)*a[n] for n in range(M+1)]
def sq(a):
    c=[0]*(M+1)
    for n in range(M+1):
        if 2*n<=M: c[2*n]=a[n]
    return c
print("(A) PARITY: odd-coefficient support of u_k")
for k in (1,2,3,4):
    odd=[n for n in range(1,M+1,2) if us[k][n]!=0]
    print(f"  u_{k}: {'EVEN SERIES (no odd terms to 300)' if not odd else f'first odd term q^{odd[0]}, count {len(odd)}'}")
print()
print("(B) log-linear identification of phi_1 = u1(q)u1(-q)/u1(q^2)")
def logser(a):
    L=[Fr(0)]*(M+1); af=[Fr(x) for x in a]
    for n in range(1,M+1):
        L[n]=af[n]-sum(Fr(j,n)*L[j]*af[n-j] for j in range(1,n))
    return L
phi1=mul(mul(us[1],negq(us[1])),inv_unit(sq(us[1])))
target=logser(phi1)
cands={}
for k in (2,3,4):
    cands[f"log u{k}(q^2)"]=logser(sq(us[k]))
    cands[f"log[u{k}(q)u{k}(-q)]"]=logser(mul(us[k],negq(us[k])))
names=list(cands)
rows=[n for n in range(2,140,2)]
import itertools
A=[[cands[nm][n] for nm in names] for n in rows]
b=[target[n] for n in rows]
aug=[row+[bv] for row,bv in zip(A,b)]
nc=len(names); r=0; piv=[]
for c in range(nc):
    pr=next((i for i in range(r,len(aug)) if aug[i][c]!=0),None)
    if pr is None: continue
    aug[r],aug[pr]=aug[pr],aug[r]
    pv=aug[r][c]; aug[r]=[x/pv for x in aug[r]]
    for i in range(len(aug)):
        if i!=r and aug[i][c]!=0:
            f=aug[i][c]; aug[i]=[x-f*y for x,y in zip(aug[i],aug[r])]
    piv.append(c); r+=1
consistent=all(row[-1]==0 for row in aug[r:])
print("  system consistent (exact solution exists on 70 rows)?", consistent)
if consistent:
    sol={names[piv[i]]:aug[i][-1] for i in range(r)}
    print("  solution:", {k:str(v) for k,v in sol.items() if v!=0})
us={int(k):v for k,v in json.load(open("ulattice_300.json")).items()}
M=300; p=(1<<61)-1
u1=[x%p for x in us[1]]; u2=[x%p for x in us[2]]; u3=[x%p for x in us[3]]
def mulp(a,b):
    c=[0]*(M+1)
    for i,ai in enumerate(a):
        if ai==0: continue
        for j in range(M+1-i):
            if b[j]: c[i+j]=(c[i+j]+ai*b[j])%p
    return c
def stretch(a,d):
    c=[0]*(M+1)
    for n in range(M+1):
        if d*n<=M: c[d*n]=a[n]
    return c
def powers(a,dmax):
    ps=[[1]+[0]*M]
    for _ in range(dmax): ps.append(mulp(ps[-1],a))
    return ps
def rank_kernel(cols,rows):
    A=[[cols[k][n] for k in range(len(cols))] for n in range(rows)]
    R=len(A); C=len(A[0]); r=0
    for cc in range(C):
        piv=next((rr for rr in range(r,R) if A[rr][cc]),None)
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        iv=pow(A[r][cc],p-2,p); A[r]=[x*iv%p for x in A[r]]
        for rr in range(R):
            if rr!=r and A[rr][cc]:
                f=A[rr][cc]; A[rr]=[(x-f*y)%p for x,y in zip(A[rr],A[r])]
        r+=1
        if r==R: break
    return r,C
def shift(a,j): return [0]*j+a[:M+1-j]
def search(tag, Xp, Yp, dq, dX, dY):
    cols=[]
    for bx in range(dX+1):
        for by in range(dY+1):
            base=mulp(Xp[bx],Yp[by])
            for j in range(dq+1): cols.append(shift(base,j))
    r,C=rank_kernel(cols,M+1)
    print(f"  {tag} deg(q,X,Y)=({dq},{dX},{dY}): {C} unk, rank {r} -> {'RELATION!' if r<C else 'none'}")
X=powers(u1,4)
print("(C) single-function Mahler P(q, u1(q), u1(q^d)) = 0")
for d in (2,3):
    Y=powers(stretch(u1,d),4)
    for (dq,dX,dY) in [(24,2,2),(16,3,3),(10,4,4)]:
        search(f"d={d}",X,Y,dq,dX,dY)
print("(D) SYSTEM search: relation among q^j * m(u1,u2,u3) * {1, u1(q^2)}")
U2=powers(u2,2); U3=powers(u3,1); Y2=stretch(u1,2)
mons=[]
for e1 in range(3):
    for e2 in range(3):
        for e3 in range(2):
            if e1+e2+e3<=2: mons.append(mulp(mulp(X[e1],U2[e2]),U3[e3]))
cols=[]
for m in mons:
    for yy in ([1]+[0]*M, Y2):
        base=mulp(m,yy)
        for j in range(14): cols.append(shift(base,j))
r,C=rank_kernel(cols,M+1)
print(f"  {C} unknowns, rank {r} -> {'RELATION!' if r<C else 'none'}")
