#!/usr/bin/env python3
"""
Build the BULK BLOCK generating series from the connectivity-aware transfer in
seam3_bulk_transfer, and compare its y=1 series to the validated relaxed bulk recursion
(0,2,2,6,2,18,6,42,18,118,50,282,...). If it matches, the transfer is correct and we can
study det(I-M)(x,y) at y=x^2 (true) for the cosine pole family.

Block GF: sum over runs (nonempty edge sequences forming a connected bulk piece) of the
weight. The transfer M(x,y) appends edges; a run STARTS via the seed (one edge) and the
block is the sum over all runs that CLOSE (no open components left).  We compute
   Block(x,y) = sum over states s of [ resolvent that starts at seed, ends when no open comp ]
Concretely we track an extra absorbing "closed" mark: a run ends when an append leaves zero
open components.  We compute that closing series directly.

Simpler exact approach matching the catalytic block: the relaxed bulk block counts CLOSED
bulk runs (the multigraph closes off -- start and end both at the trunk). We enumerate
walks in the transfer graph from seed states, accumulating weight, terminating when an
append produces the empty open-set (fully closed). Sum those.
"""
import sys
import sympy as sp
import seam3_bulk_transfer as B

x=B.x; y=B.y

def block_series(MS, Ncoef=14):
    states=B.build_states(MS)
    idx={s:i for i,s in enumerate(states)}
    # closing transitions: from state s, an append that yields empty open-set closes the run.
    # We need append results that produce NO open components. Modify append to allow m that
    # closes all. In append_bulk, newcomps empty means okc stays True only if groups empty;
    # but we 'continue' when a new strand group is (0,0). A fully closing edge has all new
    # strands paired into closed comps AND all old comps joined. That requires the produced
    # components to be... we treat "closed" as: result open-set is empty.
    # Re-run append allowing empty newcomps as a CLOSE.
    from itertools import permutations
    def append_full(state):
        comps=list(state); out=[]
        for m in range(2, MS+1, 2):
            u=m//2; dn=m//2
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
                            cost+=B.pcost(a_s,a_g,d_s,d_g); union(a_ref,d_ref)
                        groups={}
                        for ni in range(nid):
                            r=find(('new',ni)); groups.setdefault(r,[0,0])
                            kind,sg=newrefs[ni]
                            if kind=='up': groups[r][0]=sg
                            else: groups[r][1]=sg
                        closed=0
                        for ci in range(len(comps)):
                            r=find(('old',ci))
                            if not any(find(('new',ni))==r for ni in range(nid)):
                                closed+=1
                        newcomps=[]
                        bad=False
                        for r,g in groups.items():
                            if g[0]==0 and g[1]==0:
                                # a fully-closed new component (a 2-cycle): allowed, counts as closed
                                closed+=1
                            else:
                                newcomps.append((g[0],g[1]))
                        out.append((tuple(sorted(newcomps)), m+cost, closed))
        return out
    # DP over run length: weight series per open-state
    # start: seeds (after first edge). Then append until empty open-set => add to block.
    # vec[state] = polynomial weight (in x,y) of partial runs ending with that open-state.
    seeds=B.seed_states(MS)
    # seed weight: a single edge. compute its (state, xexp). Use append_full on empty state.
    vec={}
    for (ns,xp,cl) in append_full(()):
        vec[ns]=vec.get(ns, sp.Integer(0)) + x**xp * y**cl
    block=sp.Integer(0)
    # closed runs: those that reached empty open-set
    if () in vec:
        block+=vec.pop(())
    for step in range(2*Ncoef):
        nv={}
        for st,w in vec.items():
            for (ns,xp,cl) in append_full(st):
                term=w*x**xp*y**cl
                if ns==():
                    block+=term
                else:
                    nv[ns]=nv.get(ns,sp.Integer(0))+term
        # truncate in x
        vec={s: sp.series(p, x, 0, 2*Ncoef+2).removeO() for s,p in nv.items()}
        if all(p==0 for p in vec.values()): break
    bser=sp.series(block, x, 0, 2*Ncoef+2).removeO()
    # coeffs in q=x^2
    return [int(bser.coeff(x,2*n)) for n in range(Ncoef)]

if __name__=="__main__":
    MS=int(sys.argv[1]) if len(sys.argv)>1 else 4
    Nc=int(sys.argv[2]) if len(sys.argv)>2 else 10
    # y=1 (relaxed)
    import sympy
    ser=block_series(MS,Nc)
    print(f"MS={MS} block series (q-coeffs), symbolic in y:")
    print(ser)
