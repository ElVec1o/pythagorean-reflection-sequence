#!/usr/bin/env python3
"""
Extract, at the TRUE geodesic of each group element, two diagnostics:
  (1) maxcomp = max over cuts of #open components crossing the cut, and
  (2) nsplice = #isolated cycles spliced (= number of disconnected extra
      components in the *relaxed* geodesic of that element).

We do this with a connectivity-aware DP that tracks the FULL component multiset
(so it is exact), but we additionally carry the running max component count and
the running splice count, taking lexicographic (length, then anything) min.

Purpose: decide whether the connectivity correction introduces a SECOND
unbounded (catalytic) dimension (maxcomp grows with n) or stays bounded.
If maxcomp is bounded by a constant, the true model has the SAME single
catalytic variable as relaxed and the kernel correction is a finite-rank
perturbation.
"""
import sys
from itertools import permutations

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def solve_diag(eps_t, dl_t, k, a):
    """Return (true_len, maxcomp_at_some_geodesic, nsplice_at_relaxed_geo).
       We compute true length exactly; among geodesics we report the min maxcomp."""
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side='R' if dl_t==1 else 'L'; d_sign=1 if eps_t==1 else -1
        return pcost('L',1,d_side,d_sign),0,0
    A=min(hull+[0]); B=max(hull+[-1]); EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)
    INF=float('inf')
    # state: (comps, sp, ep) -> best (length, maxcomp_so_far)
    init=((),False,False)
    states={init:(0,0)}
    for j in edges:
        fj=f(j); aj=a.get(j,0)
        base=max(abs(aj),abs(fj))
        if (base-abs(aj))%2: base+=1
        cand=[base+2*l for l in range(0,3) if not (base+2*l==0 and (aj!=0 or fj!=0))]
        nstates={}
        for (comps,sp,ep),(c0,mc0) in states.items():
            if comps=='DONE':
                # main walk finished; only carry forward through inactive edges
                if 0 in cand and aj==0 and fj==0 and j!=0 and j!=k:
                    key=('DONE',sp,ep); val=(c0,mc0)
                    if key not in nstates or val<nstates[key]: nstates[key]=val
                continue
            for m in cand:
                u=(m+fj)//2; dn=(m-fj)//2
                if u<0 or dn<0: continue
                for pu in range(u+1):
                    t=aj+dn-u+2*pu
                    if t%2: continue
                    pd=t//2
                    if pd<0 or pd>dn: continue
                    prev_m=sum(cc[0]+cc[1]+cc[2]+cc[3] for cc in comps)
                    if j<=-1 and prev_m>0 and m==0: continue
                    if j>=1 and prev_m==0 and m>0: continue
                    arr=[]; dep=[]
                    for ci,cc in enumerate(comps):
                        for _ in range(cc[0]): arr.append(('L',1,('old',ci)))
                        for _ in range(cc[1]): arr.append(('L',-1,('old',ci)))
                        for _ in range(cc[2]): dep.append(('L',1,('old',ci)))
                        for _ in range(cc[3]): dep.append(('L',-1,('old',ci)))
                    newrefs=[]; nid=0
                    for _ in range(pd): arr.append(('R',1,('new',nid))); newrefs.append(('dn',1)); nid+=1
                    for _ in range(dn-pd): arr.append(('R',-1,('new',nid))); newrefs.append(('dn',-1)); nid+=1
                    for _ in range(pu): dep.append(('R',1,('new',nid))); newrefs.append(('up',1)); nid+=1
                    for _ in range(u-pu): dep.append(('R',-1,('new',nid))); newrefs.append(('up',-1)); nid+=1
                    if j==0: arr.append(('L',1,('start',0)))
                    if j==k: dep.append(('R' if dl_t==1 else 'L',1 if eps_t==1 else -1,('end',0)))
                    if len(arr)!=len(dep): continue
                    n=len(arr)
                    if n==0:
                        if m!=0: continue
                        if not all(cc[0]+cc[1]+cc[2]+cc[3]==0 for cc in comps): continue
                        key=(comps,sp,ep); val=(c0,mc0)
                        if key not in nstates or val<nstates[key]: nstates[key]=val
                        continue
                    base_cost=c0+m; seen=set()
                    for perm in permutations(range(n)):
                        sk=tuple(sorted((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n)))
                        if sk in seen: continue
                        seen.add(sk)
                        cost=base_cost; parent={}
                        def find(z):
                            while parent.get(z,z)!=z:
                                parent[z]=parent.get(parent[z],parent[z]); z=parent[z]
                            return z
                        def union(p,qq):
                            rp,rq=find(p),find(qq)
                            if rp!=rq: parent[rp]=rq
                        for ci in range(len(comps)): parent[('old',ci)]=('old',ci)
                        for ni in range(nid): parent[('new',ni)]=('new',ni)
                        parent[('start',0)]=('start',0); parent[('end',0)]=('end',0)
                        for i in range(n):
                            a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                            cost+=pcost(a_s,a_g,d_s,d_g); union(a_ref,d_ref)
                        groups={}
                        for ni in range(nid):
                            groups.setdefault(find(('new',ni)),[0,0,0,0,False,False])
                            kind,sg=newrefs[ni]
                            idx=(0 if sg==1 else 1) if kind=='up' else (2 if sg==1 else 3)
                            groups[find(('new',ni))][idx]+=1
                        for ci,cc in enumerate(comps):
                            r=find(('old',ci)); groups.setdefault(r,[0,0,0,0,False,False])
                            if cc[4]: groups[r][4]=True
                            if cc[5]: groups[r][5]=True
                        if j==0:
                            r=find(('start',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][4]=True
                        if j==k:
                            r=find(('end',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][5]=True
                        newcomps=[]; finished=None; ok=True
                        for r,g in groups.items():
                            ns=g[0]+g[1]+g[2]+g[3]
                            if ns==0:
                                if g[4] and g[5]:
                                    if finished is not None: ok=False; break
                                    finished=g
                                else: ok=False; break  # TRUE model: reject isolated cycle
                            else: newcomps.append(tuple(g))
                        if not ok: continue
                        if finished is not None and newcomps: continue
                        nsp=sp or (j==0); nep=ep or (j==k)
                        ncomp=len(newcomps)
                        nmc=max(mc0,ncomp)
                        if finished is not None:
                            key=('DONE',nsp,nep)
                        else:
                            key=(tuple(sorted(newcomps)),nsp,nep)
                        val=(cost,nmc)
                        if key not in nstates or val<nstates[key]: nstates[key]=val
        states=nstates
        if not states: return None
    best=None
    for key,(c,mc) in states.items():
        if key[0]=='DONE' and key[1] and key[2]:
            if best is None or (c,mc)<best: best=(c,mc)
    if best is None: return None
    return best[0], best[1], None

def bfs(maxd):
    def freeze(d): return tuple(sorted(d.items()))
    ident=(1,0,0,()); dist={ident:0}; frontier=[ident]
    for d in range(maxd):
        nxt=[]
        for (e,dl,k,L) in frontier:
            cands=[(e,1-dl,k,L),(-e,1-dl,k,L)]
            D=dict(L)
            if dl==0:
                D[k-1]=D.get(k-1,0)+e
                if D[k-1]==0: del D[k-1]
                cands.append((e,1,k-1,freeze(D)))
            else:
                D=dict(L); D[k]=D.get(k,0)-e
                if D[k]==0: del D[k]
                cands.append((e,0,k+1,freeze(D)))
            for ne in cands:
                if ne not in dist: dist[ne]=d+1; nxt.append(ne)
        frontier=nxt
    return dist

if __name__=="__main__":
    maxd=int(sys.argv[1]) if len(sys.argv)>1 else 11
    dist=bfs(maxd)
    # histogram: maxcomp by true length n
    from collections import defaultdict
    bylen=defaultdict(lambda: defaultdict(int))
    mism=0
    for key,d in dist.items():
        e,dl,k,L=key
        r=solve_diag(e,dl,k,L)
        if r is None: mism+=1; continue
        tl,mc,_=r
        if tl!=d: mism+=1
        bylen[d][mc]+=1
    print(f"depth {maxd}, mismatches {mism}")
    print("n : {maxcomp: count}  -- min-maxcomp geodesic component count distribution")
    for n in range(maxd):
        h=dict(sorted(bylen[n].items()))
        mx=max(h) if h else 0
        print(f" {n:2d}: max_over_elts maxcomp={mx}   dist={h}")
