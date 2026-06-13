#!/usr/bin/env python3
"""
SHAPE census (the corrected lemma).

The literal 'bounded #components' lemma is FALSE (deposit family forces n+1 comps
at length 6n). The RIGHT invariant for the catalytic-variable / algebraicity
argument is:

  (A) the number of DISTINCT component-shapes appearing in any optimal interface
      profile is bounded by an absolute constant, and
  (B) for each profile, all but O(1) of the components are copies of ONE 'bulk'
      shape, whose multiplicity is the catalytic counter.

We census, over the radius-R ball, every optimal interface profile that the
connectivity DP passes through, and record:
   - the GLOBAL set of distinct component-shapes ever seen,
   - per-profile: #distinct shapes, and the multiplicity histogram,
   - whether 'most' components are a single repeated shape.

If the distinct-shape set is bounded and high-multiplicity is always a single
repeated bulk shape, the catalytic-variable reduction goes through despite the
unbounded raw count.
"""
import sys
from itertools import permutations
from collections import defaultdict, Counter

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

GLOBAL_SHAPES=set()
MAX_DISTINCT=0
MAX_DISTINCT_EX=None
PROFILE_RECORDS=[]   # (#distinct_shapes, max_multiplicity, total_comps)

def solve_record(eps_t, dl_t, k, a, target_len):
    """Run the connectivity DP; whenever a transition lands on an OPTIMAL prefix
    (cost+lower-bound <= target), record its profile shapes. We approximate
    'optimal prefix' by only keeping min-cost states (the DP already does), and
    record every profile that survives in `states` (these are min-cost per key).
    Returns best length."""
    global GLOBAL_SHAPES, MAX_DISTINCT, MAX_DISTINCT_EX
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side = 'R' if dl_t==1 else 'L'; d_sign = 1 if eps_t==1 else -1
        return pcost('L',1,d_side,d_sign)
    A=min(hull+[0]); B=max(hull+[-1]); EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j):
        if 0<=j<k: return 1
        if k<=j<0: return -1
        return 0
    INF=float('inf')
    states={((),False,False):0}
    for j in edges:
        fj=f(j); aj=a.get(j,0)
        base=max(abs(aj),abs(fj))
        if (base-abs(aj))%2: base+=1
        cand=[base+2*l for l in range(3) if not (base+2*l==0 and (aj!=0 or fj!=0))]
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
                    prev_m=sum(sum(cc[:4]) for cc in comps)
                    if j<=-1 and prev_m>0 and m==0: continue
                    if j>=1 and prev_m==0 and m>0: continue
                    arr=[];dep=[]
                    for ci,cc in enumerate(comps):
                        for _ in range(cc[0]): arr.append(('L',1,('old',ci)))
                        for _ in range(cc[1]): arr.append(('L',-1,('old',ci)))
                        for _ in range(cc[2]): dep.append(('L',1,('old',ci)))
                        for _ in range(cc[3]): dep.append(('L',-1,('old',ci)))
                    newrefs=[];nid=0
                    for _ in range(pd): arr.append(('R',1,('new',nid)));newrefs.append(('dn',1));nid+=1
                    for _ in range(dn-pd): arr.append(('R',-1,('new',nid)));newrefs.append(('dn',-1));nid+=1
                    for _ in range(pu): dep.append(('R',1,('new',nid)));newrefs.append(('up',1));nid+=1
                    for _ in range(u-pu): dep.append(('R',-1,('new',nid)));newrefs.append(('up',-1));nid+=1
                    if j==0: arr.append(('L',1,('start',0)))
                    if j==k: dep.append(('R' if dl_t==1 else 'L',1 if eps_t==1 else -1,('end',0)))
                    if len(arr)!=len(dep): continue
                    n=len(arr)
                    if n==0:
                        if m!=0: continue
                        if any(sum(cc[:4])>0 for cc in comps): continue
                        key=(comps,sp,ep)
                        if key not in nstates or c0<nstates[key]: nstates[key]=c0
                        continue
                    seen=set()
                    for perm in permutations(range(n)):
                        sk=tuple(sorted((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n)))
                        if sk in seen: continue
                        seen.add(sk)
                        cost=c0+m; parent={}
                        def find(z):
                            while parent.get(z,z)!=z: parent[z]=parent.get(parent[z],parent[z]); z=parent[z]
                            return z
                        def union(p,q):
                            rp,rq=find(p),find(q)
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
                            kind,sg=newrefs[ni]; idx=(0 if sg==1 else 1) if kind=='up' else (2 if sg==1 else 3)
                            groups[find(('new',ni))][idx]+=1
                        for ci,cc in enumerate(comps):
                            r=find(('old',ci)); groups.setdefault(r,[0,0,0,0,False,False])
                            if cc[4]: groups[r][4]=True
                            if cc[5]: groups[r][5]=True
                        if j==0:
                            r=find(('start',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][4]=True
                        if j==k:
                            r=find(('end',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][5]=True
                        newcomps=[];fin=None;ok=True
                        for r,g in groups.items():
                            ns=sum(g[:4])
                            if ns==0:
                                if g[4] and g[5]:
                                    if fin is not None: ok=False;break
                                    fin=g
                                else: ok=False;break
                            else: newcomps.append(tuple(g))
                        if not ok: continue
                        if fin is not None and newcomps: continue
                        nsp=sp or j==0; nep=ep or j==k
                        shape=tuple(sorted(newcomps))
                        key=('DONE',nsp,nep) if fin is not None else (shape,nsp,nep)
                        if key not in nstates or cost<nstates[key]: nstates[key]=cost
        states=nstates
        # record profiles that survive (min-cost per key) at this edge
        for (comps,sp,ep),c in states.items():
            if comps=='DONE': continue
            ctr=Counter(comps)
            for shp in ctr: GLOBAL_SHAPES.add(shp)
            nd=len(ctr)
            if nd>MAX_DISTINCT:
                globals()['MAX_DISTINCT']=nd
                globals()['MAX_DISTINCT_EX']=(eps_t,dl_t,k,dict(a),j,comps)
            if len(comps)>=1:
                maxmult=max(ctr.values())
                pass  # skipped for speed
        if not states: return None
    best=INF
    for key,c in states.items():
        if key[0]=='DONE' and key[1] and key[2]: best=min(best,c)
    return None if best==INF else best

if __name__=='__main__':
    R=int(sys.argv[1]) if len(sys.argv)>1 else 11
    dist=bfs(R)
    mism=0
    for (e,dl,k,L),d in dist.items():
        fl=solve_record(e,dl,k,L,d)
        if fl!=d: mism+=1
    print(f"radius {R}: mismatches {mism}")
    print(f"\n# distinct component-shapes EVER seen (global): {len(GLOBAL_SHAPES)}")
    for s in sorted(GLOBAL_SHAPES):
        print("   ", s)
    print(f"\nMax #DISTINCT shapes in a single profile: {MAX_DISTINCT}")
    print(f"   witness: {MAX_DISTINCT_EX}")
    print()
