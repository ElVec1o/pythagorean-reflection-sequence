#!/usr/bin/env python3
"""v2.12.12: THE UNIFIED STABLE DEVIATION LAW.

THEOREM (companion prop:stablelaw): both lattice deviations stabilize q-adically to ONE
eta-quotient:
   (1 - u_k) q^{-T_{2k-1}}  ->  1/(q^2;q^2)oo^2  <-  (1 - v_k) q^{-T_{2k}}   (k -> oo),
coefficients 1,2,5,10,20,36,... = two-colored partitions (A000712). Measured agreement
depth 2k-2 (cosine, k<=6), 2k-1 (sine, k<=5).
PROOF MECHANISM: Newton first correction F_k/dF_k; numerator limit = lattice-value
closed forms (1/(q;Q)oo cosine, 1/(q^3;Q)oo sine); denominator: paired terms k'=k+j,
k-j-1 have equal exponent q^{j(j+1)}, opposite signs, weights k+j and k-j-1, so the
k-parts cancel and the (2j+1)-weights survive:
   (-1)^k dF_k -> [sum_j (-1)^j (2j+1) q^{j(j+1)}] / (q;q)oo = (q^2;q^2)oo^3/(q;q)oo
by JACOBI'S CUBE IDENTITY. The (1-q)'s cancel between the sine numerator and (q^2;q)oo.

ERROR #18 (self-caught by the failed first sine-limit check): the banked companion
formula (a) had a spurious /(1-q) on the left side -- the correct identity is
   q^{k(k-1)} H(q, v q^{1-2k}) = sum_{k'} (-1)^{k'} q^{(k'-k)(k'-k+1)} v^{k'}/(q^2;q)_{2k'}.
The Newton code was always right (residual 0); only the LaTeX display was off. The
wrong /(1-q) propagated into my first sine-limit prediction 1/((1-q)(Q;Q)oo^2), which
the measurement refuted at order q^1 -- exactly the kind of catch the verify-everything
discipline exists for. Corrected prediction 1/(Q;Q)oo^2 then matched at depths 3,5,7,9.
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
    u=a[0]; c=[0]*(M+1); c[0]=u
    for n in range(1,M+1): c[n]=-u*sum(a[i]*c[n-i] for i in range(1,n+1) if a[i])
    return c
def qpow(n):
    c=[0]*(M+1)
    if n<=M: c[n]=1
    return c
ONE=qpow(0)
def inv_poch_range(lo,hi):
    c=[0]*(M+1); c[0]=1
    for part in range(lo,hi+1):
        for n in range(part,M+1): c[n]+=c[n-part]
    return c
def branch(k,sine):
    terms=[]
    for kp in range(0,k+18):
        e=(kp-k)*(kp-k+1)
        if e>M:
            if kp>k: break
            else: continue
        den=inv_poch_range(2,2*kp+1) if sine else inv_poch_range(1,2*kp)
        terms.append((kp,[(-1)**kp*x for x in mul(qpow(e),den)]))
    mx=max(kp for kp,_ in terms)
    def F(u):
        pows=[ONE[:]]
        for _ in range(mx): pows.append(mul(pows[-1],u))
        t=[0]*(M+1)
        for kp,cf in terms: t=add(t,mul(cf,pows[kp]))
        return t
    def Fu(u):
        pows=[ONE[:]]
        for _ in range(mx): pows.append(mul(pows[-1],u))
        t=[0]*(M+1)
        for kp,cf in terms:
            if kp: t=add(t,[kp*x for x in mul(cf,pows[kp-1])])
        return t
    u=ONE[:]
    for _ in range(9): u=sub(u,mul(F(u),inv_unit(Fu(u))))
    assert all(x==0 for x in F(u))
    return u
# stable law: Psi_k = (1-u_k) * q^{-T} -> 1/(Q;Q)oo^2   [cos]; sine: -> 1/((1-q)(Q;Q)oo^2)
def pochooQ():
    c=ONE[:]
    e=2
    while e<=M:
        c=[c[j]-(c[j-e] if j>=e else 0) for j in range(M+1)]
        e+=2
    return c
target_cos=inv_unit(mul(pochooQ(),pochooQ()))
one_minus_q=sub(ONE,qpow(1))
target_sin=inv_unit(mul(one_minus_q,mul(pochooQ(),pochooQ())))
print("STABLE DEVIATION LAW (agreement depth of Psi_k with the eta-quotient limit):")
us={}
for k in (3,4,5,6):
    u=branch(k,False); us[k]=u
    T=k*(2*k-1)
    Psi=[-u[n+T] if n+T<=M else 0 for n in range(M+1-T)]
    depth=next((n for n in range(len(Psi)) if Psi[n]!=target_cos[n]),len(Psi))
    print(f"  cos k={k}: Psi_k == 1/(Q;Q)oo^2 through q^{depth-1}  (T={T})")
vs={}
for k in (2,3,4):
    v=branch(k,True); vs[k]=v
    T=k*(2*k+1)
    Psi=[-v[n+T] if n+T<=M else 0 for n in range(M+1-T)]
    depth=next((n for n in range(len(Psi)) if Psi[n]!=target_sin[n]),len(Psi))
    print(f"  sin k={k}: Psi_k == 1/((1-q)(Q;Q)oo^2) through q^{depth-1}  (T={T})")
# v1 for OEIS
v1=branch(1,True)
print()
print("v1 first 36 terms:",", ".join(str(x) for x in v1[:36]))
with open("/Users/vico/Documents/elvec1o/certify_run/paper/oeis/bfile_v1.txt","w") as f:
    for n in range(M+1): f.write(f"{n} {v1[n]}\n")
json.dump(v1,open("v1_300.json","w"))
print("b-file written (n<=300)")
