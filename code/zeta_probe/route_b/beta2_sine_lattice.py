#!/usr/bin/env python3
"""v2.12.11: THE SINE-SIDE LATTICE + THE TRIANGULAR LAW.

(a) INTEGRALITY: v_k := q^{2k-1} w_k(q) in 1 + q Z[[q]] for every k (w_k = zeros of the
q-sine H). Same exponent identity as the cosine side:
  q^{k(k-1)} H(q, v q^{1-2k})/(1-q) = sum_{k'} (-1)^{k'} q^{(k'-k)(k'-k+1)} v^{k'}/(q^2;q)_{2k'}
strictly convex Newton polygon, Hensel on every edge.
(b) LATTICE VALUES (swap-dressing on H = 1phi1(0; q^3; Q, qz)):
  H(q, q^{1-2m}) = (-1)^m [(Q;Q)oo/(q (q^3;Q)oo)] sum_r (-1)^r q^{(m+r+1)^2}/((Q;Q)_r (Q;Q)_{m+r})
  => ord_q = (m+1)^2 - 1.
(c) ONSETS: v_k = 1 - q^{k(2k+1)}(1+O(q)).
THE TRIANGULAR LAW: onset(u_k - 1) = k(2k-1) = T_{2k-1}, onset(v_k - 1) = k(2k+1) = T_{2k},
leading coefficient -1 in both: the two interleaved zero lattices switch on at every
triangular number exactly once, alternating between the cosine and sine families.
VERIFIED: v_1..v_4 integral to order 200, onsets 3, 10, 21, 36 = T_2, T_4, T_6, T_8;
closed form 44 digits at q=0.3; cosine side confirmed through u_8 (onsets 45, 66, 91,
120 = T_9, T_11, T_13, T_15).
"""
M=200
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
    """1/prod_{i=lo..hi}(1-q^i)"""
    c=[0]*(M+1); c[0]=1
    for part in range(lo,hi+1):
        for n in range(part,M+1): c[n]+=c[n-part]
    return c
def v_branch(k):
    """sine-side: F^H_k(q,v) = sum_{k'} (-1)^{k'} q^{(k'-k)(k'-k+1)} v^{k'} / (q^2;q)_{2k'}"""
    terms=[]
    for kp in range(0,k+16):
        e=(kp-k)*(kp-k+1)
        if e>M:
            if kp>k: break
            else: continue
        terms.append((kp,[(-1)**kp*x for x in mul(qpow(e),inv_poch_range(2,2*kp+1))]))
    mx=max(kp for kp,_ in terms)
    def F(v):
        pows=[ONE[:]]
        for _ in range(mx): pows.append(mul(pows[-1],v))
        t=[0]*(M+1)
        for kp,cf in terms: t=add(t,mul(cf,pows[kp]))
        return t
    def Fv(v):
        pows=[ONE[:]]
        for _ in range(mx): pows.append(mul(pows[-1],v))
        t=[0]*(M+1)
        for kp,cf in terms:
            if kp: t=add(t,[kp*x for x in mul(cf,pows[kp-1])])
        return t
    v=ONE[:]
    for _ in range(9): v=sub(v,mul(F(v),inv_unit(Fv(v))))
    assert all(x==0 for x in F(v)),f"residual k={k}"
    return v
print("SINE-SIDE LATTICE (v_k = q^{2k-1} w_k):")
for k in (1,2,3,4):
    v=v_branch(k)
    nz=[n for n in range(1,M+1) if v[n]!=0]
    T2k=k*(2*k+1)
    print(f"  v_{k}: integral={all(isinstance(x,int) for x in v)}, v_k(0)={v[0]}, onset q^{nz[0]} (predicted T_{2*k}={T2k}), lead {v[nz[0]]}")
# sine-side lattice-value closed form, numeric check
from mpmath import mp, mpf
mp.dps=45
q=mpf('0.3'); Q=q*q
def H(q,z):
    tot=mpf(1); term=mpf(1)
    for k in range(1,90):
        term*=-q**(2*k-1)*z/((1-q**(2*k))*(1-q**(2*k+1)))
        tot+=term
    return tot
def pochoo(a,Q):
    r=mpf(1); i=0
    while abs(a*Q**i)>mpf(10)**-50: r*=(1-a*Q**i); i+=1
    return r
def pochn(a,Q,n):
    r=mpf(1)
    for i in range(n): r*=(1-a*Q**i)
    return r
print()
print("sine lattice values H(q,q^{1-2m}) vs closed form:")
for m in range(4):
    lhs=H(q,q**(1-2*m))
    S=mpf(0)
    for r in range(50):
        S+=(-1)**r*q**((m+r+1)**2)/(pochn(Q,Q,r)*pochn(Q,Q,m+r))
    rhs=(-1)**m*pochoo(Q,Q)/pochoo(q**3,Q)*S/q
    print(f"  m={m}: |H - closed| = {mp.nstr(abs(lhs-rhs),3)}   ord check: |H| ~ q^{(m+1)**2-1}: {mp.nstr(abs(lhs),6)} vs {mp.nstr(q**((m+1)**2-1),6)}")
# ===== u_6..u_8 onsets + crossing-constant certificates =====
# (1) u_6, u_7, u_8 onsets: predicted T_11=66, T_13=91, T_15=120
M=130
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
def inv_poch(m):
    c=[0]*(M+1); c[0]=1
    for part in range(1,m+1):
        for n in range(part,M+1): c[n]+=c[n-part]
    return c
for k in (6,7,8):
    terms=[]
    for kp in range(0,k+13):
        e=(kp-k)*(kp-k+1)
        if e<=M: terms.append((kp,[(-1)**kp*x for x in mul(qpow(e),inv_poch(2*kp))]))
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
    for _ in range(8): u=sub(u,mul(F(u),inv_unit(Fu(u))))
    assert all(x==0 for x in F(u))
    nz=[n for n in range(1,M+1) if u[n]!=0]
    print(f"u_{k}: onset q^{nz[0]} (predicted T_{2*k-1} = {k*(2*k-1)}), lead {u[nz[0]]}")
# (2) crossing constants at 200 digits + PSLQ
from mpmath import mp, mpf, pslq
mp.dps=210
def G(q,z):
    tot=mpf(1); term=mpf(1)
    for k in range(1,60):
        term*=-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
    return tot
def H(q,z):
    tot=mpf(1); term=mpf(1)
    for k in range(1,60):
        term*=-q**(2*k-1)*z/((1-q**(2*k))*(1-q**(2*k+1)))
        tot+=term
    return tot
def thG(q,z):
    tot=mpf(0); term=mpf(1)
    for k in range(1,60):
        term*=-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=k*term
    return tot
qs=mpf(open("qstar_430.txt").read().strip())
mp.dps=400
Q=qs*qs; ws=2*qs*(1-qs)
A=G(qs,Q*ws); hs=H(qs,ws); B=thG(qs,ws)   # B here = thG at w* (nonzero at simple zero)
print()
print("crossing constants (30 digits):")
print("  A  = G(q*,Q*w*)  =",mp.nstr(A,30))
print("  h* = H(q*,w*)    =",mp.nstr(hs,30))
print("  thG(q*,w*)       =",mp.nstr(B,30))
print("  control |A h* - (1-q*)| =",mp.nstr(abs(A*hs-(1-qs)),3))
mp.dps=380
for nm,x in [("A",A),("h*",hs),("thG(w*)",B)]:
    r=pslq([x**i for i in range(9)],tol=mpf(10)**-340,maxcoeff=10**12,maxsteps=10**6)
    if r:
        v=sum(r[i]*x**i for i in range(9))
        print(f"  {nm} deg8: {'GENUINE '+str(r) if abs(v)<mpf(10)**-300 else 'spurious'}")
    else: print(f"  {nm}: no integer polynomial deg<=8 height 1e12 -- CERTIFIED")
# mixed basket: A vs q* polynomial relation?
r=pslq([mpf(1),qs,A,qs*A,qs*qs,A*A,qs*qs*A,qs*A*A,A*A*A],tol=mpf(10)**-340,maxcoeff=10**10,maxsteps=10**6)
print("  joint (q*, A) cubic basket:",("HIT "+str(r)) if r else "none (1e10) -- CERTIFIED")
