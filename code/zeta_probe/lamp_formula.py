# Geodesic length via chain DP over edges, tested against exact BFS distances.
# Model: walk on Z, moves cost 1; consecutive moves pair at the shared site:
#   pass (same direction) = 1, bounce = 0, sign-flip: free at pass, 2 at bounce.
# Virtual arrival at site 0 (side L, sign +); virtual departure at site k*
# (side R if delta*=1 else L, sign eps*).
# Edge j: m_j crossings (m_j >= |a_j|, m_j == a_j mod 2, m_j >= |f_j|, and >= 2
# on interior gap edges), u_j=(m_j+f_j)/2 ups, dn_j downs; sign split p_up, p_dn
# (# with eps=+1) with deposit constraint a_j = 2 p_dn - dn + u - 2 p_up.
# Site cost: min-cost transportation between arrivals {(L,+):..} and departures.
import sys
from functools import lru_cache
from itertools import product
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

@lru_cache(maxsize=None)
def site_cost(arr, dep):
    # arr, dep: 4-tuples (L+, L-, R+, R-) counts; min-cost matching
    # cost: same side & same sign 0; same side diff sign 2; diff side 1
    if sum(arr)!=sum(dep): return None
    n=sum(arr)
    if n==0: return 0
    # min-cost transportation via DP over departure allocation (counts small)
    # order classes; recursive allocation of arrivals class by class
    COST=[[0,2,1,1],[2,0,1,1],[1,1,0,2],[1,1,2,0]]
    best=[None]
    def rec(i, rem, acc):
        if best[0] is not None and acc>=best[0]: return
        if i==4:
            best[0]=acc if best[0] is None else min(best[0],acc)
            return
        a=arr[i]
        if a==0: rec(i+1, rem, acc); return
        # distribute a among 4 dep classes
        r0,r1,r2,r3=rem
        for x0 in range(min(a,r0)+1):
            for x1 in range(min(a-x0,r1)+1):
                for x2 in range(min(a-x0-x1,r2)+1):
                    x3=a-x0-x1-x2
                    if x3<0 or x3>r3: continue
                    c=acc+x0*COST[i][0]+x1*COST[i][1]+x2*COST[i][2]+x3*COST[i][3]
                    rec(i+1,(r0-x0,r1-x1,r2-x2,r3-x3),c)
    rec(0, dep, 0)
    return best[0]

def formula_len(eps_t, dl_t, k, a):
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull = nz+trav
    if not hull:
        # no moves possibly; but also allow m=2 excursions? cost>=2+, while
        # pure separator cost <=2: only beneficial never. match virtuals at site 0.
        arr=[0,0,0,0]; arr[0]+=1  # (L,+)
        dep=[0,0,0,0]
        side = 2 if dl_t==1 else 0
        dep[side + (0 if eps_t==1 else 1)] += 1
        return site_cost(tuple(arr),tuple(dep))
    A=min(hull+[0]); B=max(hull+[-1])
    # allow one extension edge on each side (rarely helps; cheap to include)
    EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j):
        if 0<=j<k: return 1
        if k<=j<0: return -1
        return 0
    INF=float('inf')
    # DP over edges; state = (m, p_up, p_dn) for the previous edge
    # site between edge j-1 and j is site j
    # initialize with a fictitious edge A-EXT-1 with m=0
    states={(0,0,0):0.0}
    for j in edges:
        fj=f(j); aj=a.get(j,0)
        # candidate m_j
        base=max(abs(aj),abs(fj))
        # parity: m == a == f mod 2 (consistency: a==f mod2 by normal form)
        if (base - abs(aj))%2: base+=1
        if base%2 != abs(aj)%2: base+=1
        # m=0 only possible when nothing forces a crossing (a=f=0); chain
        # reachability is enforced in the DP transition below.
        cand_m=[]
        for lam in range(0,3):
            m=base+2*lam
            if m==0 and (aj!=0 or fj!=0):
                continue
            cand_m.append(m)
        nstates={}
        for (pm,ppu,ppd),c0 in states.items():
            for m in cand_m:
                # reachability chain: edges left of the start need their
                # right-neighbour crossed; edges right of start need their
                # left-neighbour crossed.
                if j<=-1 and pm>0 and m==0: continue
                if j>=1 and pm==0 and m>0: continue
                u=(m+fj)//2; dn=(m-fj)//2
                if u<0 or dn<0: continue
                for pu in range(u+1):
                    # deposit: a = 2 pdn - dn + u - 2 pu  => pdn = (a + dn - u + 2 pu)/2
                    t=aj+dn-u+2*pu
                    if t%2: continue
                    pd=t//2
                    if pd<0 or pd>dn: continue
                    # site j: between prev edge (j-1) and this edge j
                    arr=[0,0,0,0]; dep=[0,0,0,0]
                    # arrivals: ups of edge j-1 (side L): ppu with +, pm_u- ...
                    pu_prev=ppu; u_prev=(pm + f(j-1))//2 if pm>0 or True else 0
                    u_prev=(pm + f(j-1))//2; dn_prev=(pm - f(j-1))//2
                    arr[0]+=pu_prev; arr[1]+=u_prev-pu_prev
                    # arrivals: downs of edge j (side R)
                    arr[2]+=pd; arr[3]+=dn-pd
                    # departures: downs of edge j-1 (side L)
                    pd_prev=ppd
                    dep[0]+=pd_prev; dep[1]+=dn_prev-pd_prev
                    # departures: ups of edge j (side R)
                    dep[2]+=pu; dep[3]+=u-pu
                    if j==0:
                        arr[0]+=1
                    if j==k:
                        side = 2 if dl_t==1 else 0
                        dep[side + (0 if eps_t==1 else 1)] += 1
                    sc=site_cost(tuple(arr),tuple(dep))
                    if sc is None: continue
                    val=c0+m+sc
                    key=(m,pu,pd)
                    if key not in nstates or val<nstates[key]:
                        nstates[key]=val
        states=nstates
        if not states: return None
    # final site B+EXT+1: prev edge = last, no next edge
    j=edges[-1]+1
    best=INF
    for (pm,ppu,ppd),c0 in states.items():
        arr=[0,0,0,0]; dep=[0,0,0,0]
        u_prev=(pm+f(j-1))//2; dn_prev=(pm-f(j-1))//2
        arr[0]+=ppu; arr[1]+=u_prev-ppu
        dep[0]+=ppd; dep[1]+=dn_prev-ppd
        if j==0: arr[0]+=1
        if j==k:
            side = 2 if dl_t==1 else 0
            dep[side + (0 if eps_t==1 else 1)] += 1
        sc=site_cost(tuple(arr),tuple(dep))
        if sc is None: continue
        best=min(best,c0+sc)
    return None if best==INF else best

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 10
dist=bfs(maxd)
mism=0; tested=0; examples=[]
for (e,dl,k,L),d in dist.items():
    fl=formula_len(e,dl,k,L)
    tested+=1
    if fl!=d:
        mism+=1
        if len(examples)<8: examples.append(((e,dl,k,dict(L)),d,fl))
print(f"tested {tested} elements to depth {maxd}: mismatches {mism}")
for ex in examples: print("  MISMATCH", ex)
