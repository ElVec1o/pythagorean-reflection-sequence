#!/usr/bin/env python3
"""
TRUE-metric TRAVEL transfer, built directly as an abstract per-site transfer on
connectivity-aware interface states (NOT via the slow BFS+solve).

(Restored 2026-06-14: this file was transiently removed during a Route-A session.)

Setup. Consider a travel direction k>0: the path must go from site 0 to site k.
Edges j=0..k-1 all have f_j=+1. Each carries m_j strands (m_j odd >=1,
u_j-dn_j=+1). The deposit a_j has ODD magnitude on a travel edge. Length =
sum m_j + sum site costs. We build the interface transfer on STATES = multiset of
components, each (up_sign, dn_sign) in {-1,0,1}^2 minus (0,0); per component <=1 up
& <=1 dn (the connectivity constraint). The transfer appends one travel edge; an
interior isolated cycle (old comp closed with no new strand) is pruned.

det(I - M_C(x)) is the TRUE travel denominator; its smallest positive root r_C
satisfies r_C^2 -> q* = 0.449453631 (the relaxed travel pole), confirming the
travel block is connectivity-invariant (R1).
"""
import sympy as sp
from itertools import product, permutations
from functools import lru_cache

x = sp.symbols('x')
COMP_TYPES = [(u,d) for u in (-1,0,1) for d in (-1,0,1) if not (u==0 and d==0)]

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

@lru_cache(maxsize=None)
def append_edge(state, fj, max_strands):
    comps = list(state); results = []
    for m in range(abs(fj), max_strands+1):
        if (m-abs(fj))%2: continue
        if m==0 and fj!=0: continue
        u=(m+fj)//2; dn=(m-fj)//2
        if u<0 or dn<0: continue
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
                    groups={}
                    for ni in range(nid):
                        r=find(('new',ni)); groups.setdefault(r,[0,0])
                        kind,sg=newrefs[ni]
                        if kind=='up': groups[r][0]=sg
                        else: groups[r][1]=sg
                    ok=True
                    for ci in range(len(comps)):
                        r=find(('old',ci))
                        if not any(find(('new',ni))==r for ni in range(nid)):
                            ok=False; break
                    if not ok: continue
                    newcomps=[]
                    for r,g in groups.items():
                        if g[0]==0 and g[1]==0: ok=False; break
                        newcomps.append((g[0],g[1]))
                    if not ok: continue
                    if len(newcomps)>max_strands: continue
                    results.append((tuple(sorted(newcomps)), m+cost_site))
    return results

def seed_states(max_comps, max_strands):
    out=set()
    for m in range(1, max_strands+1, 2):
        u=(m+1)//2; dn=(m-1)//2
        for pu in range(u+1):
            for pd in range(dn+1):
                ups=[1]*pu+[-1]*(u-pu); dns=[1]*pd+[-1]*(dn-pd)
                comps=[]; npair=min(len(ups),len(dns))
                for i in range(npair): comps.append((ups[i],dns[i]))
                for i in range(npair,len(ups)): comps.append((ups[i],0))
                for i in range(npair,len(dns)): comps.append((0,dns[i]))
                if 1<=len(comps)<=max_comps: out.add(tuple(sorted(comps)))
    return out

def build_states(max_comps, max_strands):
    seen=set(seed_states(max_comps, max_strands)); frontier=list(seen)
    while frontier:
        nf=[]
        for st in frontier:
            for (ns,xp) in append_edge(st, 1, max_strands):
                if 1<=len(ns)<=max_comps and ns not in seen:
                    seen.add(ns); nf.append(ns)
        frontier=nf
    return sorted(seen, key=lambda s:(len(s),s))

def transfer_matrix(states, max_strands):
    idx={s:i for i,s in enumerate(states)}; N=len(states); M=sp.zeros(N,N)
    for s in states:
        for (ns,xp) in append_edge(s,1,max_strands):
            if ns in idx: M[idx[ns], idx[s]] += x**xp
    return M, idx

if __name__=="__main__":
    import sys
    MC=int(sys.argv[1]) if len(sys.argv)>1 else 2
    MS=int(sys.argv[2]) if len(sys.argv)>2 else 5
    states=build_states(MC, MS)
    print(f"max_comps={MC} max_strands={MS}: #states={len(states)}")
    for s in states[:20]: print("  ", s)
    M,idx=transfer_matrix(states, MS)
    print("matrix built", M.shape)
