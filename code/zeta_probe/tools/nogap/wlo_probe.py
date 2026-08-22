"""Where the free pair lives.

Sharpens HasFreePair. Over all cost-minimal transition systems on n <= 4 edges with
more than one walk, there are always two BOTTOM arrivals, in different walks, at a
walk's leftmost site. Both being bottom ends they share a side, so the merge is free
(NoGapMerge.swap_free_iff).

Cost is the correct one: an arrival and its departure sharing a side is always a
sign-flipped bounce (EndData.sgn), costing 2; different sides is a pass, costing 1.
"""
exec(open("side.py").read().split("tot = multi")[0])
import itertools
def cost(E,t,up): return sum(2 if a[2]==t[a][2] else 1 for a in E if isArr(a,up))
cases=hit=0
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
                f=False
                for a in E:
                    if not isArr(a,up) or a[2]!=0: continue
                    for a2 in E:
                        if not isArr(a2,up) or a2[2]!=0: continue
                        if site(a)!=site(a2) or comp[a]==comp[a2]: continue
                        if site(a)==wlo[comp[a]] or site(a)==wlo[comp[a2]]: f=True; break
                    if f: break
                hit+=f
print("multi-walk cost-minimal cases:",cases," with two bottom arrivals at a leftmost site:",hit)
