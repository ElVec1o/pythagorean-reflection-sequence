#!/usr/bin/env python3
"""
Self-contained: build the connectivity-aware TRUE travel transfer matrix M_C(x)
over component-multiset interface states (isolated cycles pruned in the interior),
and confirm its dominant pole equals the relaxed travel pole q* = 0.449453631
(i.e. R1 / travel-invariance at the operator level), and that larger C does not
introduce a smaller pole (the true travel block's dominant singularity is q*).
"""
import sys
import mpmath as mp
from itertools import permutations
mp.mp.dps=30

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def append_edge(state, max_strands):
    """state = tuple of (up,dn) comps. Append one travel edge (f=+1). Return list of
       (new_state, xpow). Interior connectivity: a closed loop (old comp fully matched
       among itself, no new strand) is an isolated cycle -> INVALID (pruned)."""
    comps=list(state); fj=1; res=[]
    for m in range(1, max_strands+1, 2):
        u=(m+fj)//2; dn=(m-fj)//2
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
                    cost=0
                    for i in range(n):
                        a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                        cost+=pcost(a_s,a_g,d_s,d_g); union(a_ref,d_ref)
                    # prune isolated cycles: every old comp must connect to a new strand
                    ok=True
                    for ci in range(len(comps)):
                        r=find(('old',ci))
                        if not any(find(('new',ni))==r for ni in range(nid)):
                            ok=False; break
                    if not ok: continue
                    groups={}
                    for ni in range(nid):
                        r=find(('new',ni)); groups.setdefault(r,[0,0])
                        kind,sg=newrefs[ni]
                        if kind=='up': groups[r][0]=sg
                        else: groups[r][1]=sg
                    newcomps=[]
                    for r,g in groups.items():
                        if g[0]==0 and g[1]==0: ok=False; break
                        newcomps.append((g[0],g[1]))
                    if not ok: continue
                    if len(newcomps)>max_strands: continue
                    res.append((tuple(sorted(newcomps)), m+cost))
    return res

def seed(max_comps, max_strands):
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
    seen=set(seed(max_comps,max_strands)); frontier=list(seen)
    while frontier:
        nf=[]
        for st in frontier:
            for (ns,xp) in append_edge(st,max_strands):
                if 1<=len(ns)<=max_comps and ns not in seen:
                    seen.add(ns); nf.append(ns)
        frontier=nf
    return sorted(seen,key=lambda s:(len(s),s))

def det_IM(MC,MS,xval):
    states=build_states(MC,MS); n=len(states); idx={s:i for i,s in enumerate(states)}
    M=mp.zeros(n,n)
    for s in states:
        for (ns,xp) in append_edge(s,MS):
            if ns in idx: M[idx[ns],idx[s]]+=mp.mpf(xval)**xp
    return mp.det(mp.eye(n)-M), n

if __name__=="__main__":
    MS=int(sys.argv[1]) if len(sys.argv)>1 else 7
    qstar=mp.mpf('0.449453630558948'); xstar=mp.sqrt(qstar)
    print(f"q*={mp.nstr(qstar,12)} x*={mp.nstr(xstar,12)}")
    for MC in (1,2,3):
        prev=None; root=None; pq=None; x=mp.mpf('0.30')
        n=0
        while x<mp.mpf('0.66'):
            d,n=det_IM(MC,MS,x)
            if prev is not None and prev*d<0:
                root=mp.findroot(lambda z: det_IM(MC,MS,z)[0], (pq+x)/2); break
            prev=d; pq=x; x+=mp.mpf('0.01')
        if root:
            print(f"MC={MC} states={n}: 1st pole x={mp.nstr(root,10)} -> q=x^2={mp.nstr(root**2,10)}  (q*={mp.nstr(qstar,8)})")
        else:
            print(f"MC={MC} states={n}: no pole in (0.30,0.66)")
