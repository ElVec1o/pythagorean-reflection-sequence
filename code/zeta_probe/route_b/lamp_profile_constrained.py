# Connectivity-aware geodesic DP ("plumber profile"): exact word length.
# Interface state = components of partial walk crossing the current edge,
# each component = (multiset of typed strands, has_start, has_end).
# Strand types: 0=up+, 1=up-, 2=down+, 3=down-  (direction, sign).
# At each site, arrivals pair with departures (one visit each); a pairing
# merges the two components and costs: pass(sides differ)=1, bounce=0,
# sign-flip +2 at bounces, free at passes. Virtual arrival at site 0
# (side L, +); virtual departure at site k* (side per delta*, sign eps*).
# A component that loses all strands without markers (or before the end)
# is an isolated cycle => branch invalid. Exact connectivity.
import sys
from functools import lru_cache
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

# pair cost: arrival (side a_s in {L,R}, sign), departure (side, sign)
# sides L/R refer to which side of the SITE the move is on:
# arrival from below = L, from above = R; departure to below = L, above = R.
# pass <=> sides differ (cost 1, flips free); bounce <=> same side (0, flip 2)
def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def solve(eps_t, dl_t, k, a):
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        # zero moves: virtual arr (L,+) pairs virtual dep
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
    # state: (frozenset-like tuple of components, ) ; component =
    # (n_up_p, n_up_m, n_dn_p, n_dn_m, has_start, has_end) over CURRENT edge strands
    # start as: no edge yet; virtual arrival not yet placed (placed at site 0)
    # we also need start/end placed exactly once: markers tracked via flags in state:
    # (components, start_placed, end_placed) ; before site 0, start unplaced.
    init_state=( (), False, False )
    states={init_state:0}
    for j in edges:                      # process SITE j, then edge j becomes current
        fj=f(j); aj=a.get(j,0)
        base=max(abs(aj),abs(fj))
        if (base-abs(aj))%2: base+=1
        cand=[]
        for lam in range(0,3):
            m=base+2*lam
            if m==0 and (aj!=0 or fj!=0): continue
            cand.append(m)
        nstates={}
        for (comps, sp, ep), c0 in states.items():
            if comps=='DONE':
                # walk finished; valid to continue only with m=0 and no events
                if 0 in cand and aj==0 and fj==0 and j!=0 and j!=k:
                    key=(comps,sp,ep)
                    if key not in nstates or c0<nstates[key]:
                        nstates[key]=c0
                continue
            # current edge is j-1 with strands inside comps
            for m in cand:
                u=(m+fj)//2; dn=(m-fj)//2
                if u<0 or dn<0: continue
                for pu in range(u+1):
                    t=aj+dn-u+2*pu
                    if t%2: continue
                    pd=t//2
                    if pd<0 or pd>dn: continue
                    # reachability chain
                    prev_m=sum(cc[0]+cc[1]+cc[2]+cc[3] for cc in comps)
                    if j<=-1 and prev_m>0 and m==0: continue
                    if j>=1 and prev_m==0 and m>0: continue
                    # events at site j:
                    # arrivals: up-strands of edge j-1 (from comps, side L, sign per type)
                    #           down-strands of edge j (new, side R): pd of sign +, dn-pd of -
                    #           virtual arrival if j==0 (side L, +)
                    # departures: down-strands of edge j-1 (comps, side L)
                    #           up-strands of edge j (new, side R): pu +, u-pu -
                    #           virtual departure if j==k (side per dl_t, sign eps_t)
                    arr=[]; dep=[]
                    for ci,cc in enumerate(comps):
                        for _ in range(cc[0]): arr.append(('L',1,('old',ci)))
                        for _ in range(cc[1]): arr.append(('L',-1,('old',ci)))
                        for _ in range(cc[2]): dep.append(('L',1,('old',ci)))
                        for _ in range(cc[3]): dep.append(('L',-1,('old',ci)))
                    newrefs=[]
                    nid=0
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
                        # nothing happens at this site; carry state but edge becomes j (no strands)
                        # only valid if m==0 and comps empty-or-finished
                        if m!=0: continue
                        # comps must have no strands (they don't if prev edge m=0)
                        ok=True
                        for cc in comps:
                            if cc[0]+cc[1]+cc[2]+cc[3]>0: ok=False
                        if not ok: continue
                        key=(comps,sp,ep)
                        if key not in nstates or c0<nstates[key]:
                            nstates[key]=c0
                        continue
                    # enumerate pairings (n small); memo symmetry via sorting
                    # union-find over: old components (len(comps)), new strands (nid), start, end
                    base_cost=c0+m
                    seen_pair=set()
                    for perm in permutations(range(n)):
                        # canonical key to dedupe symmetric perms
                        sigkey=tuple((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n))
                        sigkey=tuple(sorted(sigkey))
                        if sigkey in seen_pair: continue
                        seen_pair.add(sigkey)
                        cost=base_cost
                        # union-find
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
                        # build new components over: new strands + markers
                        groups={}
                        for ni in range(nid):
                            groups.setdefault(find(('new',ni)),[0,0,0,0,False,False])
                            kind,sg=newrefs[ni]
                            idx = (0 if sg==1 else 1) if kind=='up' else (2 if sg==1 else 3)
                            groups[find(('new',ni))][idx]+=1
                        # markers: start marker exists if sp(placed before) in comps or placed now
                        # markers propagate: old comps with has_start/has_end
                        for ci,cc in enumerate(comps):
                            r=find(('old',ci))
                            if cc[4] or cc[5] or True:
                                groups.setdefault(r,[0,0,0,0,False,False])
                                if cc[4]: groups[r][4]=True
                                if cc[5]: groups[r][5]=True
                        if j==0:
                            r=find(('start',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][4]=True
                        if j==k:
                            r=find(('end',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][5]=True
                        # validity: any group with 0 strands must be fully closed:
                        # allowed only if it has BOTH markers (the finished path) --
                        # and even then only if nothing remains later... we allow it
                        # and require at the very end exactly one component w/ both.
                        newcomps=[]
                        finished=None
                        for r,g in groups.items():
                            ns=g[0]+g[1]+g[2]+g[3]
                            if ns==0:
                                if g[4] and g[5]:
                                    if finished is not None: ok=False; break
                                    finished=g
                                else:
                                    ok=False; break   # isolated cycle or dangling marker
                            else:
                                if g[0]+g[1]>=2 or g[2]+g[3]>=2:
                                    ok=False; break   # CONSTRAINT: <=1 up,<=1 dn per comp
                                newcomps.append(tuple(g))
                        if not ok: continue
                        if finished is not None and newcomps:
                            continue  # path closed but strands remain disconnected
                        nsp = sp or (j==0); nep = ep or (j==k)
                        if finished is not None:
                            key=('DONE', nsp, nep)
                        else:
                            key=(tuple(sorted(newcomps)), nsp, nep)
                        if key not in nstates or cost<nstates[key]:
                            nstates[key]=cost
        states=nstates
        if not states: return None
    best=INF
    for (comps,sp,ep),c in states.items():
        if comps=='DONE' and sp and ep:
            best=min(best,c)
        elif comps==() or comps==('DONE',):
            pass
    # also accept state ('DONE', True, True) form
    for key,c in states.items():
        if key[0]=='DONE' and key[1] and key[2]:
            best=min(best,c)
    return None if best==INF else best

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 9
dist=bfs(maxd)
mism=0; tested=0; ex=[]
for (e,dl,k,L),d in dist.items():
    fl=solve(e,dl,k,L)
    tested+=1
    if fl!=d:
        mism+=1
        if len(ex)<6: ex.append(((e,dl,k,dict(L)),d,fl))
print(f"profile DP: tested {tested} to depth {maxd}: mismatches {mism}")
for x in ex: print("  MISMATCH",x)
