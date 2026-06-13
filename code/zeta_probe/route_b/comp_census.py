#!/usr/bin/env python3
"""
Connectivity-boundedness census.

We re-run the EXACT connectivity-aware profile DP (lamp_profile.solve) but
instrument it to record, along every OPTIMAL (length-minimizing) reconstruction,
the maximum number of simultaneously-open interface components crossing any
single edge.

Question (Route B lemma): is max-open-components bounded by an absolute constant
on geodesics?  Census in the paper claims <= 7.  We reproduce and stratify it,
and we hunt for the extremal family.

Output:
  - histogram of  max_open_components  over all geodesics in the ball of radius R
  - the elements that realize the maximum
  - growth of the maximum with R
"""
import sys, os
from itertools import permutations
from collections import defaultdict

def freeze(d): return tuple(sorted(d.items()))

def bfs(maxd):
    ident=(1,0,0,())
    dist={ident:0}; frontier=[ident]
    for d in range(maxd):
        nxt=[]
        for (e,dl,k,L) in frontier:
            cands=[(e,1-dl,k,L), (-e,1-dl,k,L)]
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
                if ne not in dist:
                    dist[ne]=d+1; nxt.append(ne)
        frontier=nxt
    return dist

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def solve_instrumented(eps_t, dl_t, k, a):
    """Returns (best_length, max_open_comps_on_some_optimal_path).
    State value = (cost, max_comps_so_far). We minimise cost; among equal cost we
    keep the one with the SMALLEST max_comps (so the reported max is the minimum
    over optimal reconstructions -- i.e. a geodesic CAN be realised with at most
    this many open comps).  We ALSO track the max-over-optimal for contrast."""
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side = 'R' if dl_t==1 else 'L'
        d_sign = 1 if eps_t==1 else -1
        return pcost('L',1,d_side,d_sign), (0,0)
    A=min(hull+[0]); B=max(hull+[-1])
    EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j):
        if 0<=j<k: return 1
        if k<=j<0: return -1
        return 0
    INF=float('inf')
    init_state=( (), False, False )
    # value: (cost, min_maxcomps_among_optimal, max_maxcomps_among_optimal)
    states={init_state:(0,0,0)}
    for j in edges:
        fj=f(j); aj=a.get(j,0)
        base=max(abs(aj),abs(fj))
        if (base-abs(aj))%2: base+=1
        cand=[]
        for lam in range(0,3):
            m=base+2*lam
            if m==0 and (aj!=0 or fj!=0): continue
            cand.append(m)
        nstates={}
        def relax(key, cost, mn, mx):
            if key not in nstates:
                nstates[key]=(cost,mn,mx); return
            (c0,mn0,mx0)=nstates[key]
            if cost<c0:
                nstates[key]=(cost,mn,mx)
            elif cost==c0:
                nstates[key]=(c0, min(mn0,mn), max(mx0,mx))
        for (comps, sp, ep), (c0,mn0,mx0) in states.items():
            ncur=len(comps)
            if comps=='DONE':
                if 0 in cand and aj==0 and fj==0 and j!=0 and j!=k:
                    relax((comps,sp,ep), c0, mn0, mx0)
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
                    if j==k:
                        dep.append(('R' if dl_t==1 else 'L', 1 if eps_t==1 else -1, ('end',0)))
                    if len(arr)!=len(dep): continue
                    n=len(arr)
                    if n==0:
                        if m!=0: continue
                        ok=True
                        for cc in comps:
                            if cc[0]+cc[1]+cc[2]+cc[3]>0: ok=False
                        if not ok: continue
                        relax((comps,sp,ep), c0, mn0, mx0)
                        continue
                    base_cost=c0+m
                    seen_pair=set()
                    for perm in permutations(range(n)):
                        sigkey=tuple((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n))
                        sigkey=tuple(sorted(sigkey))
                        if sigkey in seen_pair: continue
                        seen_pair.add(sigkey)
                        cost=base_cost
                        parent={}
                        def find(z):
                            while parent.get(z,z)!=z:
                                parent[z]=parent.get(parent[z],parent[z]); z=parent[z]
                            return z
                        def union(p,q):
                            rp,rq=find(p),find(q)
                            if rp!=rq: parent[rp]=rq
                        for ci in range(len(comps)): parent[('old',ci)]=('old',ci)
                        for ni in range(nid): parent[('new',ni)]=('new',ni)
                        parent[('start',0)]=('start',0); parent[('end',0)]=('end',0)
                        ok=True
                        for i in range(n):
                            a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                            cost+=pcost(a_s,a_g,d_s,d_g)
                            union(a_ref,d_ref)
                        groups={}
                        for ni in range(nid):
                            groups.setdefault(find(('new',ni)),[0,0,0,0,False,False])
                            kind,sg=newrefs[ni]
                            idx = (0 if sg==1 else 1) if kind=='up' else (2 if sg==1 else 3)
                            groups[find(('new',ni))][idx]+=1
                        for ci,cc in enumerate(comps):
                            r=find(('old',ci))
                            groups.setdefault(r,[0,0,0,0,False,False])
                            if cc[4]: groups[r][4]=True
                            if cc[5]: groups[r][5]=True
                        if j==0:
                            r=find(('start',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][4]=True
                        if j==k:
                            r=find(('end',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][5]=True
                        newcomps=[]; finished=None
                        for r,g in groups.items():
                            ns=g[0]+g[1]+g[2]+g[3]
                            if ns==0:
                                if g[4] and g[5]:
                                    if finished is not None: ok=False; break
                                    finished=g
                                else:
                                    ok=False; break
                            else:
                                newcomps.append(tuple(g))
                        if not ok: continue
                        if finished is not None and newcomps: continue
                        nsp = sp or (j==0); nep = ep or (j==k)
                        # number of OPEN components on edge j (after this site) =
                        # len(newcomps); record max over the chain so far
                        nopen=len(newcomps)
                        nmn=max(mn0,nopen); nmx=max(mx0,nopen)
                        if finished is not None:
                            key=('DONE', nsp, nep)
                        else:
                            key=(tuple(sorted(newcomps)), nsp, nep)
                        relax(key, cost, nmn, nmx)
        states=nstates
        if not states: return None, None
    best=INF; best_mn=None; best_mx=None
    for key,(c,mn,mx) in states.items():
        if key[0]=='DONE' and key[1] and key[2]:
            if c<best:
                best=c; best_mn=mn; best_mx=mx
            elif c==best:
                best_mn=min(best_mn,mn); best_mx=max(best_mx,mx)
    if best==INF: return None,None
    return best, (best_mn, best_mx)

if __name__=='__main__':
    maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
    dist=bfs(maxd)
    hist_min=defaultdict(int)   # min over optimal reconstructions
    hist_max=defaultdict(int)   # max over optimal reconstructions
    extremal_min=defaultdict(list)
    by_radius_min=defaultdict(int)  # max min-comps seen at each radius
    by_radius_max=defaultdict(int)
    tested=0; mism=0
    for (e,dl,k,L),d in dist.items():
        fl, comps = solve_instrumented(e,dl,k,L)
        tested+=1
        if fl!=d:
            mism+=1
            continue
        mn,mx=comps
        hist_min[mn]+=1
        hist_max[mx]+=1
        if mn>=3 and len(extremal_min[mn])<8:
            extremal_min[mn].append((d,(e,dl,k,dict(L))))
        by_radius_min[d]=max(by_radius_min[d], mn)
        by_radius_max[d]=max(by_radius_max[d], mx)
    print(f"radius {maxd}: tested {tested}, mismatches {mism}")
    print("\nHistogram of MIN-over-optimal open-component count (geodesic-realisable):")
    for c in sorted(hist_min): print(f"  {c:2d} open comps : {hist_min[c]:6d} elements")
    print("\nHistogram of MAX-over-optimal open-component count:")
    for c in sorted(hist_max): print(f"  {c:2d} open comps : {hist_max[c]:6d} elements")
    print("\nMax MIN-open-comps as a function of radius:")
    for d in sorted(by_radius_min): print(f"  r={d:2d}: min-side max={by_radius_min[d]}  max-side max={by_radius_max[d]}")
    print("\nExtremal elements (high min-open-comps):")
    for c in sorted(extremal_min):
        for d,g in extremal_min[c]:
            print(f"  min-open={c} at length {d}: {g}")
