#!/usr/bin/env python3
"""v2.12.13: THE BETA_2 FAMILY -- S has infinitely many real zeros, one per lattice branch,
accumulating at q = 1 with the CLASSICAL COSINE-ZERO LAW.

DISCOVERY PATH (and a self-caught artifact): a scan of c(q) = z1(q)/(q(1-q)) appeared to jump
discontinuously at q ~ 0.85, suggesting a positive-axis fold. The zero-landscape map REFUTED
this: the ladder never collides on (0,1); the jump was the bisection bracket landing on a
higher branch (z3) -- artifact of a naive [0,b] bracket among crowding zeros. The true
structure is richer:

 - as q -> 1, every branch falls like (1-q)^2 (confluent limit to classical Bessel/cosine
   zeros) while the parabola w = 2q(1-q) falls like (1-q): w overtakes EVERY branch once;
 - hence S(q) = G(q, 2q(1-q)) has infinitely many zeros q*_1 < q*_2 < ... -> 1, with
   w(q*_j) = z_j(q*_j)  [verified at j=2: w - z_2 = 9.8e-43, exactly one zero below w];
 - accumulation law: 1 - q*_j ~ 8/(pi^2 (2j-1)^2); measured law ratios (j = 1..8):
   0.679, 0.961, 0.986, 0.993, 0.9956, 0.9970, 0.9979, 0.9984 -> 1.

THE SECOND MEMBER (new constants): q*_2 = 0.913486638731047141696... (110 digits in
family_roots.json), beta_2^(2) = 1/sqrt(q*_2) = 1.046282352687417855...
Certificates: neither q*_2 nor beta_2^(2) satisfies an integer polynomial of degree <= 8,
height 1e10; no bilinear relation between q*_1 and q*_2 (1e8, 100 digits).

READING: the family interpolates between the OPEN head (j=1: beta_2 itself, the wild one)
and the CLASSICAL tail (pi^2-law, transcendence-friendly world): the step-ratio mechanism's
confluent boundary visible inside a single object. Combinatorial status of higher roots
(subdominant singularities of the original GF) NOT verified -- dictionary only established
at the dominant root.
"""
from mpmath import mp, mpf, matrix, lu_solve, pslq
mp.dps=60
def G(q,z,K=100):
    tot=mp.mpf(1); term=mp.mpf(1)
    for k in range(1,K):
        term*=-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
    return tot
def Gz(q,z,K=100):
    tot=mp.mpf(0); term=mp.mpf(1)
    for k in range(1,K):
        term*=-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=k*term/z
    return tot
def Gq(q,z):
    h=mpf(10)**-25
    return (G(q+h,z)-G(q-h,z))/(2*h)
# (a) zero landscape on (0,3) for q in [0.70,0.90]
print("real zeros of G(q,.) in (0,3):")
for qq in ['0.70','0.74','0.76','0.78','0.80','0.82','0.86','0.90']:
    q=mpf(qq); zeros=[]
    prev=G(q,mpf('0.001')); zprev=mpf('0.001')
    z=mpf('0.001')
    while z<3:
        z+=mpf('0.004'); cur=G(q,z)
        if prev*cur<0:
            a,b=zprev,z
            for _ in range(80):
                m=(a+b)/2
                if G(q,a)*G(q,m)<0: b=m
                else: a=m
            zeros.append((a+b)/2)
        prev,zprev=cur,z
    print(f"  q={qq}: {[mp.nstr(x,8) for x in zeros]}")
# ===== the family, the law, the certificates =====
from mpmath import mp, mpf, pi, sqrt, pslq
mp.dps=130
def S(q,K=140):
    w=2*q*(1-q)
    tot=mp.mpf(1); term=mp.mpf(1)
    for k in range(1,K):
        term*=-q**(2*(k-1))*w/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
    return tot
def G(q,z,K=140):
    tot=mp.mpf(1); term=mp.mpf(1)
    for k in range(1,K):
        term*=-q**(2*(k-1))*z/((1-q**(2*k-1))*(1-q**(2*k)))
        tot+=term
    return tot
# locate zeros of S by scanning then bisecting; predictions 1-8/(pi^2(2j-1)^2)
print("the beta_2 family: zeros of S in (0,1)")
print("  j | q*_j (certified sign change) | 1-8/(pi^2(2j-1)^2) | law ratio (1-q*_j)(2j-1)^2 pi^2/8")
qs=[]
seeds=[(mpf('0.44'),mpf('0.46'))]
for j in range(2,9):
    c=1-8/(pi**2*(2*j-1)**2)
    seeds.append((c-mpf('0.03')*4**(2-j) if j>2 else c-mpf('0.03'), c+mpf('0.02')))
for j,(a,b) in enumerate(seeds,1):
    # refine bracket by scan
    n=60; found=False
    fa=S(a)
    for i in range(1,n+1):
        x=a+(b-a)*i/n; fx=S(x)
        if fa*fx<0:
            lo,hi=a+(b-a)*(i-1)/n,x; found=True; break
        fa=fx
    if not found: print(f"  {j} | no sign change in seed window ({mp.nstr(a,8)},{mp.nstr(b,8)})"); continue
    for _ in range(450):
        m=(lo+hi)/2
        if S(lo)*S(m)<0: hi=m
        else: lo=m
    root=(lo+hi)/2; qs.append(root)
    pred=1-8/(pi**2*(2*j-1)**2)
    ratio=(1-root)*(2*j-1)**2*pi**2/8
    print(f"  {j} | {mp.nstr(root,25)} | {mp.nstr(pred,12)} | {mp.nstr(ratio,10)}")
# identify branch of second zero: w(q*_2) equals which zero of G?
q2=qs[1]; w2=2*q2*(1-q2)
print()
print("branch check at q*_2: G(q*_2, w(q*_2)) =",mp.nstr(abs(G(q2,w2)),3))
# count zeros of G below w2 at q2: scan
cnt=0; prev=G(q2,mpf('1e-6')); z=mpf('1e-6')
while z<w2:
    z+=w2/4000; cur=G(q2,z)
    if prev*cur<0: cnt+=1
    prev=cur
print(f"zeros of G(q*_2,.) strictly below w(q*_2): {cnt}  (so w = z_{cnt+1}: expect z_2)")
print()
print("beta_2^(2) := 1/sqrt(q*_2) =",mp.nstr(1/sqrt(q2),30))
mp.dps=120
for nm,x in [("q*_2",q2),("beta_2^(2)",1/sqrt(q2))]:
    r=pslq([x**i for i in range(9)],tol=mpf(10)**-100,maxcoeff=10**10,maxsteps=10**6)
    if r:
        v=sum(r[i]*x**i for i in range(9))
        print(f"  {nm}: candidate {r} -> {'GENUINE' if abs(v)<mpf(10)**-90 else 'spurious'}")
    else: print(f"  {nm}: no integer polynomial deg<=8 height 1e10")
r=pslq([mpf(1),qs[0],q2,qs[0]*q2,qs[0]**2,q2**2],tol=mpf(10)**-100,maxcoeff=10**8,maxsteps=10**6)
print("  joint (q*_1, q*_2) bilinear:",r if r else "none (1e8)")
import json
json.dump([mp.nstr(x,110) for x in qs],open("family_roots.json","w"))
