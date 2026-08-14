#!/usr/bin/env python3
"""
ROUTE A: connectivity-corrected catalytic transfer.

Goal: build the TRUE series u_n from a component-aware transfer, in a form whose
kernel/denominator structure is explicit, and test it against the exact u_n.

STRUCTURAL REDUCTION (the no-isolated-cycle constraint).
========================================================
A group element is encoded by a deposited crossing-vector (m_j) on the integer
line plus markers s=0, e=k*.  This is a MULTIGRAPH Gamma on the path of sites:
slot j carries m_j parallel edges.  Lengths:
   length = sum_j m_j  +  sum_sites Site(.)        (Site = max-coupling, Lemma C)
The RELAXED length minimizes this over deposits realizing the element, IGNORING
connectivity of Gamma.  The TRUE length additionally requires Gamma to admit a
SINGLE Euler trail s->e (be connected on its nonzero part); each extra connected
component (isolated cycle) costs +2 to splice into the main trail.

Equivalent for the geodesic: an element whose cheapest relaxed deposit makes
Gamma DISCONNECTED pays an extra +2 per isolated component (or must pick a more
expensive connected deposit, whichever is cheaper).  The defect d_n = v_n - u_n
counts exactly this connectivity penalty.

This file: a component-COUNT-aware transfer.  We add to the catalytic state a
flag tracking whether the partial multigraph to the left of the cut is, on its
own support, CONNECTED to the current edge's strands; isolated components that
have already closed off are charged +2 (true) or +0 (relaxed).  By toggling the
splice cost between 0 and 2 we reproduce v_n (cost 0) and u_n (cost 2) from ONE
transfer -- exhibiting U = V - D structurally.

We validate against exact u_n and v_n.
"""
import sys
from functools import lru_cache
from itertools import permutations

# ---- exact data ----
U=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,
   17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,
   1697179,2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,
   65932461,98849591,147969934]
V=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,
   19949,30640,46905,71699,109490,166969,254047,386192,586349,889599,1347444,
   2039911,3084135,4661368,7035665,10617513,16002526,24117471,36303371,54649900,
   82171011]

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def solve(eps_t, dl_t, k, a, splice):
    """Exact connectivity-aware length with isolated-cycle splice cost = `splice`.
       splice=2 -> true length u; splice=0 -> relaxed length v.
       This is lamp_profile.solve, but instead of REJECTING a closed strand-free
       component without both markers, we charge `splice` and keep going."""
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side = 'R' if dl_t==1 else 'L'
        d_sign = 1 if eps_t==1 else -1
        return pcost('L',1,d_side,d_sign)
    A=min(hull+[0]); B=max(hull+[-1])
    EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j):
        if 0<=j<k: return 1
        if k<=j<0: return -1
        return 0
    INF=float('inf')
    # state: (components, start_placed, end_placed, finished_main)
    # component = (up+,up-,dn+,dn-, has_start, has_end)
    init_state=( (), False, False, False )
    states={init_state:0}
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
        for (comps, sp, ep, mainfin), c0 in states.items():
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
                    if j>=1 and prev_m==0 and m>0 and not mainfin: pass
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
                        ok=all(cc[0]+cc[1]+cc[2]+cc[3]==0 for cc in comps)
                        if not ok: continue
                        key=(comps,sp,ep,mainfin)
                        if key not in nstates or c0<nstates[key]: nstates[key]=c0
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
                        def union(p,qq):
                            rp,rq=find(p),find(qq)
                            if rp!=rq: parent[rp]=rq
                        for ci in range(len(comps)): parent[('old',ci)]=('old',ci)
                        for ni in range(nid): parent[('new',ni)]=('new',ni)
                        parent[('start',0)]=('start',0); parent[('end',0)]=('end',0)
                        for i in range(n):
                            a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                            cost+=pcost(a_s,a_g,d_s,d_g)
                            union(a_ref,d_ref)
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
                                    # isolated cycle: splice cost
                                    extra+=splice
                                else:
                                    ok=False; break  # dangling single marker: invalid
                            else:
                                newcomps.append(tuple(g))
                        if not ok: continue
                        nmainfin = mainfin or (finished is not None)
                        nsp = sp or (j==0); nep = ep or (j==k)
                        key=(tuple(sorted(newcomps)), nsp, nep, nmainfin)
                        cc2=cost+extra
                        if key not in nstates or cc2<nstates[key]: nstates[key]=cc2
        states=nstates
        if not states: return None
    best=INF
    for (comps,sp,ep,mainfin),c in states.items():
        if mainfin and sp and ep and all(cc[0]+cc[1]+cc[2]+cc[3]==0 for cc in comps):
            best=min(best,c)
    return None if best==INF else best

def bfs(maxd):
    def freeze(d): return tuple(sorted(d.items()))
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

if __name__=="__main__":
    maxd=int(sys.argv[1]) if len(sys.argv)>1 else 9
    dist=bfs(maxd)
    # count by length for splice=2 (true) and splice=0 (relaxed)
    cntU={}; cntV={}; misU=0; misV=0
    for key,d in dist.items():
        e,dl,k,L=key
        lu=solve(e,dl,k,L,2); lv=solve(e,dl,k,L,0)
        if lu!=d: misU+=1
        cntU[lu]=cntU.get(lu,0)+1
        cntV[lv]=cntV.get(lv,0)+1
    # The bfs dist IS the true distance, so solve(.,splice=2) should match d:
    print(f"splice=2 matches BFS true distance: mismatches={misU} over {len(dist)} elts (depth {maxd})")
    seqU=[cntU.get(n,0) for n in range(maxd)]
    seqV=[cntV.get(n,0) for n in range(maxd)]
    print("u_n (splice=2):", seqU)
    print("ref u_n       :", U[:maxd])
    print("MATCH u:", seqU==U[:maxd])
    print("v_n (splice=0):", seqV)
    print("ref v_n       :", V[:maxd])
    print("MATCH v:", seqV==V[:maxd])
