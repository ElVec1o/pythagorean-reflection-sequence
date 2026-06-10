# Uniform-in-T universality certificate at depth D.
#
# THEOREM SHAPE: a shape-specific collision at depth <= D requires a nonzero
# same-class difference D(t) with D(zeta_T)=0. Heights: |coeffs| <= depth (Lemma,
# induction: each generator adds a polynomial of height 1). Rational root thm
# over Z[i]: lambda | lead => c = N(lambda) <= (2D)^2. So:
#   * triangles with c > 4D^2: universal at depth D unconditionally;
#   * triangles with c <= 4D^2: FINITE list; for each, evaluate the entire
#     symbolic ball at zeta mod q (one-sided exact: distinct mod q => distinct).
#     If #distinct (class, value) == ball size, NO extra collision => universal.
import sys, time, math
import numpy as np

T0=time.time()
D = int(sys.argv[1]) if len(sys.argv)>1 else 23

# ---------- Pass 1: symbolic BFS ----------
# element = (eps, delta, k, P) ; P stored as canonical tuple of (exp, coef)
def compose(g, h):
    eg,dg,kg,Pg = g; eh,dh,kh,Ph = h
    if dg==0:
        items = [(e+kg, eg*c) for e,c in Ph]
    else:
        items = [(-e+kg, eg*c) for e,c in Ph]
    Q = dict(items)
    for e,c in Pg:
        Q[e]=Q.get(e,0)+c
        if Q[e]==0: del Q[e]
    if dg==0: return (eg*eh, dh, kg+kh, tuple(sorted(Q.items())))
    else:     return (eg*eh, 1-dh, kg-kh, tuple(sorted(Q.items())))

GENS=[(1,1,0,()), (-1,1,0,()), (1,1,-1,((-1,-1),(0,1)))]
ident=(1,0,0,())
seen={ident}; frontier=[ident]; counts=[1]; ball=[ident]
for d in range(D):
    nxt=[]
    for el in frontier:
        for g in GENS:
            ne=compose(g,el)
            if ne not in seen:
                seen.add(ne); nxt.append(ne)
    counts.append(len(nxt)); ball.extend(nxt); frontier=nxt
print(f"[{time.time()-T0:6.1f}s] BFS done. depth {D}, ball {len(ball)}")
print("layer counts:", counts)
EXPECT=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
        11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236]
assert counts == EXPECT[:D+1], "SYMBOLIC COUNTS DO NOT MATCH UNIVERSAL SEQUENCE"
print("symbolic counts == universal sequence: OK")

# ---------- flatten ball ----------
cls_map={}; cls_id=np.empty(len(ball),dtype=np.int64)
offs=[0]; exps=[]; coefs=[]
for i,(e,dl,k,P) in enumerate(ball):
    key=(e,dl,k)
    cls_id[i]=cls_map.setdefault(key,len(cls_map))
    for ex,c in P: exps.append(ex); coefs.append(c)
    offs.append(len(exps))
offs=np.array(offs[:-1],dtype=np.int64)   # reduceat start indices
exps=np.array(exps,dtype=np.int64); coefs=np.array(coefs,dtype=np.int64)
print(f"[{time.time()-T0:6.1f}s] flat terms {len(exps)}, classes {len(cls_map)}")
EMIN,EMAX=int(exps.min()),int(exps.max())
has_terms = np.zeros(len(ball),dtype=bool)
lens=np.diff(np.append(offs,len(exps))); has_terms = lens>0

# ---------- primes ----------
def is_prime(n):
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def find_q(start):
    q=start
    while True:
        if q%4==1 and is_prime(q): return q
        q+=1
Q1=find_q(2_000_000_000); Q2=find_q(1_900_000_000)
def sqrt_m1(q):
    for z in range(2,200):
        i=pow(z,(q-1)//4,q)
        if i*i%q==q-1: return i
    raise RuntimeError

# ---------- candidates ----------
BOUND=4*D*D
cands=[]   # (x,y,c)
LIM=2*BOUND   # both-odd case: c=(x^2+y^2)/2 <= 4D^2  =>  x^2+y^2 <= 8D^2
import math as m
for x in range(2,int(m.isqrt(LIM))+1):
    for y in range(1,x):
        s=x*x+y*y
        if s>LIM: break
        if m.gcd(x,y)!=1: continue
        c = s//2 if (x%2==1 and y%2==1) else s
        if c<=BOUND: cands.append((x,y,c))
print(f"[{time.time()-T0:6.1f}s] candidate triangles with c <= {BOUND}: {len(cands)}")

# ---------- Pass 2: evaluate ball mod q at each candidate zeta ----------
def check(q, todo):
    iq=sqrt_m1(q)
    coefs_q=(coefs % q).astype(np.uint64)
    exps_off=(exps-EMIN).astype(np.int64)
    bad=[]
    for (x,y,c) in todo:
        num=(x + y*iq) % q; den=(x - y*iq) % q
        z = num * pow(int(den), q-2, q) % q
        zin= pow(int(z), q-2, q)
        # power table for exponents EMIN..EMAX
        npow=EMAX-EMIN+1
        pw=np.empty(npow,dtype=np.uint64)
        v=pow(int(z), 0, q)
        # build z^(EMIN..EMAX)
        v0=pow(int(z), EMIN, q) if EMIN>=0 else pow(int(zin), -EMIN, q)
        cur=v0
        for j in range(npow):
            pw[j]=cur; cur=cur*z % q
        vals = coefs_q * pw[exps_off] % q          # uint64 products < 2^62
        sums = np.add.reduceat(vals, offs) % q     # per-element P(zeta) mod q
        sums = np.where(has_terms, sums, 0)
        keyarr = cls_id.astype(np.uint64)*np.uint64(q) + sums
        ndist = len(np.unique(keyarr))
        if ndist != len(ball): bad.append((x,y,c,len(ball)-ndist))
    return bad

bad1=check(Q1,cands)
print(f"[{time.time()-T0:6.1f}s] pass mod {Q1}: {len(bad1)} candidates need recheck")
final=check(Q2,bad1) if bad1 else []
print(f"[{time.time()-T0:6.1f}s] after second prime {Q2}: {len(final)} REAL suspects")
for f in final: print("   SUSPECT:", f)
if not final:
    print(f"\nCERTIFIED: universality holds at all depths <= {D} for EVERY")
    print(f"unequal-leg rational triangle: c > {BOUND} by the height theorem;")
    print(f"all {len(cands)} candidates with c <= {BOUND} verified collision-free.")
