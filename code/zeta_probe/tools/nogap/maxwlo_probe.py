"""The canonical site for the free merge.

Let s* be the MAXIMUM, over walks, of a walk's leftmost edge. At site s* there are
always two BOTTOM arrivals lying in different walks. Both bottom means they share a
side, so the merge is free (NoGapMerge.swap_free_iff).

This removes the existential over sites: s* is determined by the datum.

Verified 1114/1114 over cost-minimal transition systems on n <= 4 edges with m in
{2,4} and up in 0..4. For comparison, the same test at the MINIMUM leftmost edge
(equivalently at site 0) holds in only 662 of 1114.

Cost is the correct one: an arrival and its departure sharing a side is always a
sign-flipped bounce (EndData.sgn), costing 2; different sides is a pass, costing 1.
"""
# `side.py` was this directory's `side_probe.py` under its former name; the
# rename left this reference dangling, so this script could not run at all.
# Resolve it relative to THIS file, not the working directory.
import os as _os
_here = _os.path.dirname(_os.path.abspath(__file__))
exec(open(_os.path.join(_here, "side_probe.py")).read().split("tot = multi")[0])
import itertools
def cost(E,t,up): return sum(2 if a[2]==t[a][2] else 1 for a in E if isArr(a,up))
cases=maxw=minw=0
for n in (1,2,3,4):
    for m in itertools.product((2,4), repeat=n):
        for up in itertools.product(range(0,5), repeat=n):
            if any(u>mm for u,mm in zip(up,m)): continue
            E=ends(n,m); T=list(turns(E,up) or [])
            if not T: continue
            best=min(cost(E,t,up) for t in T)
            for t in T:
                if cost(E,t,up)!=best: continue
                comp,c=walks(E,t)
                if c<2: continue
                cases+=1
                wlo={}
                for x in E: wlo.setdefault(comp[x],[]).append(x[0])
                wlo={k:min(v) for k,v in wlo.items()}
                def pair_at(s):
                    A=[a for a in E if site(a)==s and a[2]==0 and isArr(a,up)]
                    return len({comp[a] for a in A})>=2
                maxw+=pair_at(max(wlo.values())); minw+=pair_at(min(wlo.values()))
print("multi-walk cost-minimal cases:",cases)
print("  two bottom arrivals in different walks at the MAX leftmost site:",maxw)
print("  ... at the MIN leftmost site (= site 0):",minw)
