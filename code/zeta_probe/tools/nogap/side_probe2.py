"""Shared-side probe, with the CORRECT transition cost.

For an arrival a and its departure t[a], EndData.sgn gives sgn a = D and
sgn t[a] = !D when the two share a side, so a same-side pair is ALWAYS a
sign-flipped bounce costing 2; a different-side pair is a pass costing 1.
Minimising cost therefore MAXIMISES passes.

An earlier version of this probe scored bounces 0 and passes 1 -- exactly
backwards -- and reported spurious failures.
"""
exec(open("side.py").read().split("tot = multi")[0])
import itertools

def cost(E,t,up):
    return sum(2 if a[2]==t[a][2] else 1 for a in E if isArr(a,up))

tot=multi=ok=bad=0
for n in (1,2,3):
    for m in itertools.product((2,4), repeat=n):
        for up in itertools.product(range(0,5), repeat=n):
            if any(u>mm for u,mm in zip(up,m)): continue
            E=ends(n,m); T=list(turns(E,up) or [])
            if not T: continue
            best=min(cost(E,t,up) for t in T)
            for t in T:
                if cost(E,t,up)!=best: continue
                tot+=1
                comp,c=walks(E,t)
                if c<2: continue
                multi+=1
                found=False
                for a in E:
                    if not isArr(a,up): continue
                    for a2 in E:
                        if not isArr(a2,up): continue
                        if site(a)!=site(a2) or comp[a]==comp[a2]: continue
                        if a[2]==a2[2] or t[a][2]==t[a2][2]: found=True; break
                    if found: break
                ok += found; bad += (not found)
print("cost-minimal turns:",tot," multi-walk:",multi," shared-side pair exists:",ok," none:",bad)
