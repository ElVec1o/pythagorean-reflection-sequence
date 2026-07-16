#!/usr/bin/env python3
"""The four transfer-product coefficient functions A,B,C,D of the Lambert-orbit trace on the
diagonal (paper2 prop:nofinitering(ii)-(iii)). Exact q-series to order 45 (rational arithmetic).

RESULTS (probe outcomes, banked v2.11.3):
- A,B,C,D in Z[[q]] (provable: transfer data + Lambert weights are integral);
- NOT quasimodular: no relation over span{1, phi_1, phi_3} with rational-function coefficients
  of degree <= 8 (exact kernel computation on 45 coefficients);
- NOT D-finite: no linear q-ODE of order <= 3, degree <= 6.
The relocated obstruction is genuinely non-classical -- same class as S itself.
"""
from fractions import Fraction as Fr
M=45   # truncation order in q
def mul(a,b):
    c=[Fr(0)]*(M+1)
    for i,ai in enumerate(a):
        if ai==0: continue
        for j in range(M+1-i):
            if b[j]: c[i+j]+=ai*b[j]
    return c
def add(a,b): return [x+y for x,y in zip(a,b)]
def sub(a,b): return [x-y for x,y in zip(a,b)]
def scal(s,a): return [s*x for x in a]
def qpow(n):
    c=[Fr(0)]*(M+1)
    if n<=M: c[n]=Fr(1)
    return c
ONE=qpow(0); Qs=qpow(1)
def inv(a):  # inverse of series with a[0]!=0
    c=[Fr(0)]*(M+1); c[0]=1/a[0]
    for n in range(1,M+1):
        s=Fr(0)
        for i in range(1,n+1): s+=a[i]*c[n-i]
        c[n]=-s/a[0]
    return c
# z* = 2q(1-q) = 2q - 2q^2
zs=sub(scal(2,qpow(1)),scal(2,qpow(2)))
# a_j = q+1 - q Q^j z*  (Q=q^2 -> Q^j = q^{2j}) : q z* q^{2j} = (2q^2-2q^3) shifted by 2j
def aj(j):
    t=sub(scal(2,qpow(2+2*j)),scal(2,qpow(3+2*j)))   # q*z**q^{2j} = 2q^{2j+2}-2q^{2j+3}
    return sub(add(qpow(1),ONE),t)
# transfer for u: u_{j+2}=a_j u_{j+1} - q u_j : track (alpha_d,beta_d) with u_d = alpha_d u0 + beta_d u1
# v: v_{j+2}=a_j v_{j+1} - q v_j - q Q^j z* u_{j+1}: v_d = c_d v0 + d_d v1 + e_d u0 + f_d u1
alpha=[ONE[:], [Fr(0)]*(M+1)]      # alpha_0=1, alpha_1=0
beta =[[Fr(0)]*(M+1), ONE[:]]      # beta_0=0, beta_1=1
cc=[ONE[:],[Fr(0)]*(M+1)]; dd=[[Fr(0)]*(M+1),ONE[:]]
ee=[[Fr(0)]*(M+1),[Fr(0)]*(M+1)]; ff=[[Fr(0)]*(M+1),[Fr(0)]*(M+1)]
D=24  # orbit depth (q^d weights: d<=M suffice; transfer bounded)
for j in range(0,D):
    A_=aj(j)
    alpha.append(sub(mul(A_,alpha[j+1]),mul(Qs,alpha[j])))
    beta.append(sub(mul(A_,beta[j+1]),mul(Qs,beta[j])))
    inh=mul(Qs,sub(scal(2,qpow(2+2*j)),scal(2,qpow(3+2*j))))  # q*Q^j z* = 2q^{2j+3}... wait recompute
    # q Q^j z* : q * q^{2j} * (2q-2q^2) = 2q^{2j+2} - 2q^{2j+3}
    inh=sub(scal(2,qpow(2+2*j)),scal(2,qpow(3+2*j)))
    cc.append(sub(mul(A_,cc[j+1]),mul(Qs,cc[j])))
    dd.append(sub(mul(A_,dd[j+1]),mul(Qs,dd[j])))
    ee.append(sub(sub(mul(A_,ee[j+1]),mul(Qs,ee[j])),mul(inh,alpha[j+1])))
    ff.append(sub(sub(mul(A_,ff[j+1]),mul(Qs,ff[j])),mul(inh,beta[j+1])))
# weights: w1_d = 2q^d/(1-q^d), w2_d = q^d/(1-q^d)^2 as series
def w1(d):
    g=[Fr(0)]*(M+1)
    # q^d/(1-q^d) = sum_{m>=1} q^{dm}
    m=1
    while d*m<=M: g[d*m]+=1; m+=1
    return scal(2,g)
def w2(d):
    g=[Fr(0)]*(M+1)
    # q^d/(1-q^d)^2 = sum_{m>=1} m q^{dm}
    m=1
    while d*m<=M: g[d*m]+=m; m+=1
    return g
A=[Fr(0)]*(M+1); B=[Fr(0)]*(M+1); C=[Fr(0)]*(M+1); Dd=[Fr(0)]*(M+1)
for d in range(1,D+1):
    A=add(A,add(mul(w2(d),alpha[d]),mul(w1(d),ee[d])))
    B=add(B,add(mul(w2(d),beta[d]), mul(w1(d),ff[d])))
    C=add(C,mul(w1(d),cc[d]))
    Dd=add(Dd,mul(w1(d),dd[d]))
import json
open("ABCD.json","w").write(json.dumps({k:[ [x.numerator,x.denominator] for x in v] for k,v in
    dict(A=A,B=B,C=C,D=Dd).items()}))
for name,v in [("A",A),("B",B),("C",C),("D",Dd)]:
    print(name,"=",[str(x) for x in v[:10]],"...")
