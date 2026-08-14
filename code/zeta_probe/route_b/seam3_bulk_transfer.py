#!/usr/bin/env python3
"""
SEAM #3 -- connectivity-aware BULK transfer (analog of travel_true_transfer for f=0 edges).

A bulk run is a sequence of edges with f=0 (no travel indicator) carrying even deposits
a=2s (s>=1) or gaps (m=2 forced).  The crossing multigraph must form a single Euler
structure attached to the trunk; each closed-off isolated component costs +2 (true) / +0
(relaxed).  We build the interface transfer M(x, y) where:
  - state = multiset of open components, each (up_sign, dn_sign) in {-1,0,1}^2\{(0,0)};
  - appending one edge (f=0, crossing count m even >=0; m=0 => no edge, skip; deposit
    a=2 pd - dn + u - 2 pu) pays x^m * x^{sitecost};
  - when an old component closes WITHOUT joining a new strand: RELAXED keeps it free (it is
    a legitimate separate piece), TRUE charges y (= x^2 splice) -- this is the cycle marker.

The block GF is (I - M)^{-1} seeded/closed appropriately; the DENOMINATOR is det(I - M(x,y)).
We compute det(I - M(x,y)) as a polynomial/series and:
  (1) verify y=1 reproduces the relaxed bulk block series (0,2,2,6,2,18,...);
  (2) read the TRUE (y=x^2) denominator and locate its zeros in q=x^2; test whether they
      form an infinite family accumulating at q=1 (cosine oscillation).

NOTE: for an EXACT finite transfer we bound #components <= MC and #strands per edge <= MS;
the q-series is exact up to the truncation order (super-geometric tail).  We compare the
y=1 series to the validated relaxed bulk recursion to fix correctness.
"""
import sys
from itertools import permutations
from functools import lru_cache
import sympy as sp

x = sp.symbols('x')
y = sp.symbols('y')   # cycle marker; relaxed y=1, true y=x^2

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

# Append one BULK edge (f=0) to a state = tuple of components (up,dn), up,dn in {-1,0,1}.
# Returns list of (newstate, xexp, ycount) where ycount = #components that CLOSED this step
# (i.e. old comps that did not connect to any new strand) -- charged y in the true metric.
@lru_cache(maxsize=None)
def append_bulk(state, MS):
    comps=list(state); out=[]
    fj=0
    # m even (f=0 => m even), m>=0. m=0 means an empty edge (gap with no crossing) -- but a
    # bulk edge inside a run is either a deposit (m=|a|=2s) or a forced gap (m=2). We include
    # m in {2,4,...,MS}; m=0 handled separately as "no edge".
    for m in range(2, MS+1, 2):
        u=m//2; dn=m//2   # f=0 => u=dn=m/2
        for pu in range(u+1):
            for pd in range(dn+1):
                arr=[]; dep=[]
                for ci,c in enumerate(comps):
                    if c[0]!=0: arr.append(('L',c[0],('old',ci)))
                    if c[1]!=0: dep.append(('L',c[1],('old',ci)))
                newrefs=[]; nid=0
                for _ in range(pd): arr.append(('R',1,('new',nid))); newrefs.append(('dn',1)); nid+=1
                for _ in range(dn-pd): arr.append(('R',-1,('new',nid))); newrefs.append(('dn',-1)); nid+=1
                for _ in range(pu): dep.append(('R',1,('new',nid))); newrefs.append(('up',1)); nid+=1
                for _ in range(u-pu): dep.append(('R',-1,('new',nid))); newrefs.append(('up',-1)); nid+=1
                if len(arr)!=len(dep): continue
                n=len(arr)
                if n==0: continue
                seen=set()
                for perm in permutations(range(n)):
                    sig=tuple(sorted((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n)))
                    if sig in seen: continue
                    seen.add(sig)
                    parent={}
                    def find(z):
                        while parent.get(z,z)!=z: parent[z]=parent.get(parent[z],parent[z]); z=parent[z]
                        return z
                    def union(p,q):
                        rp,rq=find(p),find(q)
                        if rp!=rq: parent[rp]=rq
                    for ci in range(len(comps)): parent[('old',ci)]=('old',ci)
                    for ni in range(nid): parent[('new',ni)]=('new',ni)
                    cost_site=0
                    for i in range(n):
                        a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                        cost_site+=pcost(a_s,a_g,d_s,d_g); union(a_ref,d_ref)
                    # group new strands into components
                    groups={}
                    for ni in range(nid):
                        r=find(('new',ni)); groups.setdefault(r,[0,0])
                        kind,sg=newrefs[ni]
                        if kind=='up': groups[r][0]=sg
                        else: groups[r][1]=sg
                    # which OLD comps closed (did not connect to any new strand)?
                    closed=0
                    for ci in range(len(comps)):
                        r=find(('old',ci))
                        if not any(find(('new',ni))==r for ni in range(nid)):
                            closed+=1
                    newcomps=[]
                    okc=True
                    for r,g in groups.items():
                        if g[0]==0 and g[1]==0: okc=False; break
                        # only keep components that are still open (have a free strand to the right)
                        newcomps.append((g[0],g[1]))
                    if not okc: continue
                    if len(newcomps)>MS: continue
                    out.append((tuple(sorted(newcomps)), m+cost_site, closed))
    return out

def seed_states(MS):
    # a single bulk edge starting a run: f=0, m even>=2
    out=set()
    for m in range(2,MS+1,2):
        u=m//2; dn=m//2
        for pu in range(u+1):
            for pd in range(dn+1):
                ups=[1]*pu+[-1]*(u-pu); dns=[1]*pd+[-1]*(dn-pd)
                comps=[]; npair=min(len(ups),len(dns))
                for i in range(npair): comps.append((ups[i],dns[i]))
                for i in range(npair,len(ups)): comps.append((ups[i],0))
                for i in range(npair,len(dns)): comps.append((0,dns[i]))
                if comps: out.add(tuple(sorted(comps)))
    return out

def build_states(MS):
    seen=set(seed_states(MS)); frontier=list(seen)
    while frontier:
        nf=[]
        for st in frontier:
            for (ns,xp,cl) in append_bulk(st,MS):
                if ns and ns not in seen:
                    seen.add(ns); nf.append(ns)
        frontier=nf
    return sorted(seen,key=lambda s:(len(s),s))

def transfer(states, MS):
    idx={s:i for i,s in enumerate(states)}; N=len(states)
    M=sp.zeros(N,N)
    for s in states:
        for (ns,xp,cl) in append_bulk(s,MS):
            if ns in idx:
                M[idx[ns],idx[s]]+= x**xp * (y**cl)
    return M, idx

if __name__=="__main__":
    MS=int(sys.argv[1]) if len(sys.argv)>1 else 4
    states=build_states(MS)
    print(f"MS={MS}: #states={len(states)}")
    M,idx=transfer(states,MS)
    print("transfer built", M.shape)
    det=sp.det(sp.eye(len(states))-M)
    print("det(I-M) computed; expanding in x...")
    detp=sp.expand(det)
    print("det(I-M)(x,y) =", detp)
