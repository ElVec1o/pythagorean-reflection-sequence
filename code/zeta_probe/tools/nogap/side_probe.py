import itertools, sys
from collections import defaultdict

def ends(n, m):
    return [(e, i, t) for e in range(n) for i in range(m[e]) for t in (0,1)]

def site(x): return x[0] + (1 if x[2] else 0)
def isUp(x, up): return x[1] < up[x[0]]
def isArr(x, up): return isUp(x, up) == bool(x[2])
def partner(x): return (x[0], x[1], 1-x[2])

def turns(E, up):
    """all involutions pairing arrivals with departures at each site"""
    bysite = defaultdict(lambda: ([], []))
    for x in E:
        (bysite[site(x)][0] if isArr(x, up) else bysite[site(x)][1]).append(x)
    per = []
    for s,(A,D) in bysite.items():
        if len(A) != len(D): return          # unbalanced: no turn exists
        per.append([list(zip(A, pd)) for pd in itertools.permutations(D)])
    for combo in itertools.product(*per):
        t = {}
        for pairs in combo:
            for a,d in pairs: t[a]=d; t[d]=a
        yield t

def walks(E, t):
    seen = {}; c = 0
    for x in E:
        if x in seen: continue
        c += 1; stack=[x]
        while stack:
            y = stack.pop()
            if y in seen: continue
            seen[y] = c
            stack += [partner(y), t[y]]
    return seen, c

tot = multi = ok = bad = 0
for n in (1,2):
    for m in itertools.product((2,4), repeat=n):
        for up in itertools.product(range(0,5), repeat=n):
            if any(u > mm for u,mm in zip(up,m)): continue
            E = ends(n, m)
            for t in (turns(E, up) or []):
                tot += 1
                comp, c = walks(E, t)
                if c < 2: continue
                multi += 1
                found = False
                for a in E:
                    for a2 in E:
                        if not (isArr(a,up) and isArr(a2,up)): continue
                        if site(a) != site(a2) or comp[a] == comp[a2]: continue
                        if a[2] == a2[2] or t[a][2] == t[a2][2]:
                            found = True; break
                    if found: break
                if found: ok += 1
                else:
                    bad += 1
                    if bad <= 2:
                        print("NO VALID PAIR: n=%d m=%s up=%s walks=%d" % (n,m,up,c))
print("turns:", tot, " multi-walk:", multi, " have a shared-side pair:", ok, " none:", bad)
