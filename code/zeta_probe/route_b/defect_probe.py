#!/usr/bin/env python3
# Instrumented true-vs-relaxed solver.
# For each group element (eps,delta,k; a) we compute:
#   - relaxed_len  : min cost over ALL realizations (any # components)
#   - true_len     : min cost over CONNECTED (single-trail) realizations
#   - At the relaxed optimum, the min number of EXTRA components (isolated cycles).
# Goal: confirm  true_len - relaxed_len == 2 * (min # isolated cycles among
#       relaxed-optimal realizations), i.e. the +2 splice law.
#
# We do this by a DP that tracks (components, sp, ep) AND total cost, but instead
# of forbidding isolated cycles, we COUNT them: each time a component closes with
# 0 strands and is NOT the (start&end) path, it is an isolated cycle (allowed in
# relaxed, +2 to splice for true). We track cost as a pair: relaxed cost and
# splice surcharge = 2*#cycles. The true length is then min over realizations of
# (relaxed_cost + 2*#cycles) where the final config has the path closed AND every
# cycle is "spliceable" (touches the hull -- automatically true here since cycles
# live on edges in the span). We compute both minima.
import sys
from itertools import permutations

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

# DP returning dict: (cost_relaxed, ncycles_at_that_realization) reachable minima.
# To get both true and relaxed we track, per interface-state, the Pareto frontier
# of (relaxed_cost, ncycles). We keep for each state a dict mapping
# relaxed_cost -> min ncycles (and overall we want min relaxed_cost, and
# min over realizations of relaxed_cost+2*ncycles among the FINISHED states).
def solve(eps_t, dl_t, k, a):
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side = 'R' if dl_t==1 else 'L'
        d_sign = 1 if eps_t==1 else -1
        c=pcost('L',1,d_side,d_sign)
        return c, c, 0   # relaxed, true, ncycles
    A=min(hull+[0]); B=max(hull+[-1])
    EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j):
        if 0<=j<k: return 1
        if k<=j<0: return -1
        return 0
    INF=float('inf')
    init_state=( (), False, False )
    # state -> dict( (relaxed_cost) -> min ncycles )
    states={init_state:{0:0}}
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
        def push(key, rc, nc):
            d=nstates.setdefault(key,{})
            if rc not in d or nc<d[rc]:
                d[rc]=nc
        for (comps, sp, ep), costmap in states.items():
            if comps=='DONE':
                if 0 in cand and aj==0 and fj==0 and j!=0 and j!=k:
                    for rc,nc in costmap.items(): push((comps,sp,ep),rc,nc)
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
                        for rc,nc in costmap.items(): push((comps,sp,ep),rc,nc)
                        continue
                    seen_pair=set()
                    for perm in permutations(range(n)):
                        sigkey=tuple((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n))
                        sigkey=tuple(sorted(sigkey))
                        if sigkey in seen_pair: continue
                        seen_pair.add(sigkey)
                        addcost=m
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
                        for i in range(n):
                            a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                            addcost+=pcost(a_s,a_g,d_s,d_g)
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
                        ok=True
                        newcomps=[]; finished=None; ncyc_new=0
                        for r,g in groups.items():
                            ns=g[0]+g[1]+g[2]+g[3]
                            if ns==0:
                                if g[4] and g[5]:
                                    if finished is not None: ok=False; break
                                    finished=g
                                elif (not g[4]) and (not g[5]):
                                    # isolated cycle: ALLOWED in relaxed, count it
                                    ncyc_new+=1
                                else:
                                    ok=False; break  # dangling single marker (invalid)
                            else:
                                newcomps.append(tuple(g))
                        if not ok: continue
                        if finished is not None and newcomps:
                            continue
                        nsp = sp or (j==0); nep = ep or (j==k)
                        if finished is not None:
                            key=('DONE', nsp, nep)
                        else:
                            key=(tuple(sorted(newcomps)), nsp, nep)
                        for rc,nc in costmap.items():
                            push(key, rc+addcost, nc+ncyc_new)
        states=nstates
        if not states: return None
    # collect finished states
    relaxed=INF; true=INF
    for key,costmap in states.items():
        if key[0]=='DONE' and key[1] and key[2]:
            for rc,nc in costmap.items():
                if rc<relaxed: relaxed=rc
                if rc+2*nc<true: true=rc+2*nc
    if relaxed==INF: return None
    # also need ncycles AT the relaxed optimum
    ncyc_at_opt=INF
    for key,costmap in states.items():
        if key[0]=='DONE' and key[1] and key[2]:
            for rc,nc in costmap.items():
                if rc==relaxed and nc<ncyc_at_opt: ncyc_at_opt=nc
    return relaxed, true, ncyc_at_opt

if __name__=="__main__":
    maxd=int(sys.argv[1]) if len(sys.argv)>1 else 9
    dist=bfs(maxd)
    # cross-check: true == BFS distance; and relaxed+2*ncyc(opt) >= true,
    # and the +2 splice law: true - relaxed == 2*ncyc_min_among_true_opt? test
    mism_true=0; tested=0; splice_ok=0; splice_bad=0
    from collections import Counter
    relaxed_hist=Counter(); true_hist=Counter()
    examples_disagree=[]
    for (e,dl,k,L),dd in dist.items():
        res=solve(e,dl,k,L)
        tested+=1
        if res is None:
            print("NONE at",(e,dl,k,dict(L))); continue
        relaxed,true,ncyc=res
        true_hist[true]+=1
        relaxed_hist[relaxed]+=1
        if true!=dd:
            mism_true+=1
            if len(examples_disagree)<6:
                examples_disagree.append(((e,dl,k,dict(L)),dd,res))
    print(f"tested {tested} to depth {maxd}: true-vs-BFS mismatches {mism_true}")
    for x in examples_disagree: print("  TRUE-MISMATCH",x)
    # Build u_n and v_n from histograms
    U=[true_hist.get(n,0) for n in range(maxd+1)]
    V=[relaxed_hist.get(n,0) for n in range(maxd+1)]
    print("u_n (true) :", U)
    print("v_n (relax):", V)
    print("d_n        :", [V[n]-U[n] for n in range(maxd+1)])
