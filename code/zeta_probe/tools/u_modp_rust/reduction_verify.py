#!/usr/bin/env python3
# Verify the explicit reduction  F(q,1) = Psi / (1 - Psi_odd),  with Psi, Psi_odd FIXED
# explicit series (no unknown G1).  Integer q-series, exact, to order M.
from fractions import Fraction as Fr
M = 40
def Z(): return [0]*(M+1)
def add(a,b): return [a[i]+b[i] for i in range(M+1)]
def smul(c,a): return [c*a[i] for i in range(M+1)]
def mul(a,b):
    r=Z()
    for i in range(M+1):
        if a[i]==0: continue
        for j in range(M+1-i):
            r[i+j]+=a[i]*b[j]
    return r
def geom(m):                       # 1/(1-q^m) = sum q^{mj}
    r=Z()
    j=0
    while m*j<=M: r[m*j]=1; j+=1
    return r
def qpow(a):                       # q^a
    r=Z()
    if a<=M: r[a]=1
    return r

# D(q^a) = 2q(q-1)q^a/((1-q^{a+1})(1-q^{a+2}))  as a series
def D_at(a):
    num=Z()
    if a+1<=M: num[a+1]+=-2
    if a+2<=M: num[a+2]+=2
    return mul(mul(num,geom(a+1)),geom(a+2))

# Psi (even telescoping factor, with (1+G1) divided out):
#   Psi = sum_k [prod_{i<k} D(q^{2i})] * 2 q^{2k+1}/(1-q^{2k+1})
def build(parity):                 # parity 0 -> even (Psi), 1 -> odd (Psi_odd)
    S=Z(); prod=Z(); prod[0]=1     # empty product = 1
    k=0
    while True:
        if parity==0:
            efac=mul(smul(2,qpow(2*k+1)),geom(2*k+1))
            low=(k+1)**2
        else:
            efac=mul(smul(2,qpow(2*k+2)),geom(2*k+2))
            low=k*k+3*k+2
        if low>M: break
        S=add(S, mul(prod,efac))
        # multiply prod by D(q^{2k+parity})  for next k
        prod=mul(prod, D_at(2*k+parity))
        k+=1
    return S
Psi=build(0); Psi_odd=build(1)

# F(q,1) = sum_s F_s(q) via the section recursion (exact integers), to order M
def Fq1():
    F={s:Z() for s in range(1,M+1)}
    def shift(a,s):
        r=Z()
        for i in range(M+1):
            if i+s<=M: r[i+s]=a[i]
        return r
    for _ in range(M+2):
        nf={}
        for s in range(1,M+1):
            t=Z()
            if s<=M: t[s]=2
            S2=Z()
            for sp in range(s,M+1): S2=add(S2,shift(F[sp],sp))
            t2=shift(smul(2,S2),s)
            S3=Z()
            for sp in range(1,s): S3=add(S3,F[sp])
            t3=shift(smul(2,S3),2*s)
            nf[s]=add(add(t,t2),t3)
        F=nf
    G=Z()
    for s in range(1,M+1): G=add(G,F[s])
    return G
G0=Fq1()

# check:  G0 * (1 - Psi_odd) - Psi == 0
one_minus=Z(); one_minus[0]=1
for i in range(M+1): one_minus[i]-=Psi_odd[i]
lhs=mul(G0,one_minus)
diff=[lhs[i]-Psi[i] for i in range(M+1)]
print("F(q,1)   [q^0..q^14]:", G0[:15])
print("Psi      [q^0..q^14]:", Psi[:15])
print("Psi_odd  [q^0..q^14]:", Psi_odd[:15])
print("G0*(1-Psi_odd)-Psi   :", diff[:25], "..." if any(diff[25:]) else "(all 0 beyond)")
print("REDUCTION HOLDS to order", M, ":", all(d==0 for d in diff))
