#!/usr/bin/env python3
"""
Locate the connectivity defect: which group elements have true_len > relaxed_len,
and what do they look like?  Uses the VALIDATED true DP (lamp_profile.solve) for
the true length and a relaxed DP (same but isolated cycles free) for relaxed.

We import the validated solvers directly to avoid reintroducing bugs.

Output:
  - the minimal-length defect elements and their (eps,delta,k,deposit) structure;
  - confirmation that PURE-TRAVEL elements (deposit supported only on [0,k), all
    |a_j| odd matching f) never have a defect;
  - the defect series d_n via the difference of the two exact length histograms,
    enumerated over a BOUNDED element family (so it is exact up to the radius where
    that family is complete).
"""
import sys
from itertools import permutations

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def _solve(eps_t,dl_t,k,a,reject_cycles):
    """If reject_cycles: TRUE length (isolated cycle invalid).
       Else: RELAXED length (isolated cycle free)."""
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side='R' if dl_t==1 else 'L'; d_sign=1 if eps_t==1 else -1
        return pcost('L',1,d_side,d_sign)
    A=min(hull+[0]); B=max(hull+[-1]); EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)
    INF=float('inf')
    init=((),False,False)
    states={init:0}
    for j in edges:
        fj=f(j); aj=a.get(j,0)
        base=max(abs(aj),abs(fj))
        if (base-abs(aj))%2: base+=1
        cand=[base+2*l for l in range(0,3) if not (base+2*l==0 and (aj!=0 or fj!=0))]
        nstates={}
        for (comps,sp,ep),c0 in states.items():
            if comps=='DONE':
                if 0 in cand and aj==0 and fj==0 and j!=0 and j!=k:
                    key=(comps,sp,ep)
                    if key not in nstates or c0<nstates[key]: nstates[key]=c0
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
                        key=(comps,sp,ep)
                        if key not in nstates or c0<nstates[key]: nstates[key]=c0
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
                        newcomps=[]; finished=None; ok=True; extra=0
                        for r,g in groups.items():
                            ns=g[0]+g[1]+g[2]+g[3]
                            if ns==0:
                                if g[4] and g[5]:
                                    if finished is not None: ok=False; break
                                    finished=g
                                elif (not g[4]) and (not g[5]):
                                    if reject_cycles: ok=False; break
                                    else: extra+=0  # relaxed: free
                                else: ok=False; break
                            else: newcomps.append(tuple(g))
                        if not ok: continue
                        if finished is not None and newcomps: continue
                        nsp=sp or (j==0); nep=ep or (j==k)
                        if finished is not None: key=('DONE',nsp,nep)
                        else: key=(tuple(sorted(newcomps)),nsp,nep)
                        v=cost+extra
                        if key not in nstates or v<nstates[key]: nstates[key]=v
        states=nstates
        if not states: return None
    best=INF
    for key,c in states.items():
        if key[0]=='DONE' and key[1] and key[2]: best=min(best,c)
    return None if best==INF else best

def true_len(e,dl,k,a): return _solve(e,dl,k,a,True)
def relaxed_len(e,dl,k,a): return _solve(e,dl,k,a,False)

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
    # Verify true_len matches BFS, and locate defects (true>relaxed).
    mism=0; defects=[]
    pure_travel_defect=0
    for key,d in dist.items():
        e,dl,k,L=key
        tl=true_len(e,dl,k,L); rl=relaxed_len(e,dl,k,L)
        if tl!=d: mism+=1
        if tl>rl:
            # classify: is the support inside [0,k) (pure travel) or does it have bulk?
            supp=[j for j in dict(L) if dict(L)[j]!=0]
            if k>0: inside=all(0<=j<k for j in supp)
            elif k<0: inside=all(k<=j<0 for j in supp)
            else: inside=(len(supp)==0)
            # pure travel = support inside travel interval AND all deposits odd
            allodd=all(abs(dict(L)[j])%2==1 for j in supp)
            ptr = inside and allodd
            if ptr: pure_travel_defect+=1
            if len(defects)<12: defects.append((key,tl,rl,tl-rl,ptr))
    print(f"depth {maxd}: true_len vs BFS mismatches = {mism}  (should be 0)")
    print(f"#defect elements (true>relaxed) in ball: {sum(1 for key,d in dist.items() if true_len(*key)>relaxed_len(*key))}")
    print(f"#PURE-TRAVEL defect elements: {pure_travel_defect}  (hypothesis: 0)")
    print("sample defect elements (key, true, relaxed, gap, pure_travel?):")
    for x in defects: print("  ",x)
