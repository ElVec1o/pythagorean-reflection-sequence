#!/usr/bin/env python3
"""
Where do isolated cycles live?  For each group element g (enumerated by BFS to
radius N), compute relaxed_len(g) and the minimum number of isolated cycles
c(g) among relaxed-OPTIMAL realizations (so true_len = relaxed_len + 2 c(g)).
Then classify every cycle-bearing element (c>=1) by:
  - whether it has travel (k != 0) or is pure-bulk (k == 0);
  - the location of the cycle relative to the travel interval [min(0,k),max(0,k)].

Uses the validated solvers:
  lamp_profile.solve     -> TRUE length (connectivity enforced)   == BFS dist
  defect_probe.solve     -> (relaxed_len, true_len, c_at_relaxed_opt)
We re-verify true_len == BFS dist as a correctness gate.
"""
import sys
sys.path.insert(0,'/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe')
sys.path.insert(0,'/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/route_b')
from lamp_profile import bfs
from defect_probe import solve as dp_solve   # returns (relaxed, true, ncyc_at_opt)
from collections import Counter, defaultdict

def main(N):
    dist=bfs(N)
    cyc=[]            # (relaxed_len, c, k, lamp_support, in_travel?)
    mism=0; tested=0
    vN=defaultdict(int); uN=defaultdict(int)
    for (e,dl,k,L),d in dist.items():
        res=dp_solve(e,dl,k,L)
        tested+=1
        if res is None: continue
        relaxed,true,c=res
        if true!=d: mism+=1
        # tally v_n (relaxed) and u_n (true)
        vN[relaxed]+=1; uN[true]+=1
        if c>=1:
            supp=sorted(j for j in L if L[j]!=0)
            K0,K1=min(0,k),max(0,k)
            cyc.append((relaxed,true,c,e,dl,k,supp,K0,K1))
    print(f"# tested {tested} to radius {N}; true-vs-BFS mismatches={mism}")
    # report v_n,u_n,d_n built from this solver (sanity vs reference)
    U=[uN.get(n,0) for n in range(N+1)]
    Vv=[vN.get(n,0) for n in range(N+1)]
    print("u_n:",U)
    print("v_n:",Vv)
    print("d_n:",[Vv[n]-U[n] for n in range(N+1)])
    # classify cycle elements
    print(f"\n# cycle-bearing elements (c>=1): {len(cyc)}")
    by_travel=Counter()
    by_c=Counter()
    travel_overlap=Counter()   # does the lamp support (where the cycle sits) lie
                               # inside / outside / straddle the travel interval?
    for relaxed,true,c,e,dl,k,supp,K0,K1 in cyc:
        by_c[c]+=1
        if k==0:
            by_travel['pure-bulk (k=0)']+=1
        else:
            by_travel['has-travel (k!=0)']+=1
        # cycle location heuristic: extra even crossings show up as lamp deposits
        # a_j with |a_j| even >=2 OR as an excess m beyond forced.  Here we use the
        # lamp support outside [K0,K1] (strictly bulk) vs inside.
        if not supp:
            travel_overlap['empty-lamp']+=1
        else:
            outside=[j for j in supp if j<K0 or j>=K1]
            inside =[j for j in supp if K0<=j<K1]
            if inside and outside: travel_overlap['straddle']+=1
            elif inside:           travel_overlap['lamp-inside-travel']+=1
            else:                  travel_overlap['lamp-outside-travel(bulk)']+=1
    print("by travel presence:",dict(by_travel))
    print("by cycle count c:  ",dict(sorted(by_c.items())))
    print("lamp vs travel interval:",dict(travel_overlap))
    # show smallest examples
    cyc.sort()
    print("\nsmallest 30 cycle elements (relaxed,true,c | eps,dl,k, lamp_support):")
    for relaxed,true,c,e,dl,k,supp,K0,K1 in cyc[:30]:
        print(f"  rl={relaxed} tl={true} c={c} | e={e} dl={dl} k={k} supp={supp} travel=[{K0},{K1})")

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 11
    main(N)
