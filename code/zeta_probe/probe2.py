# For every pair of distinct elements in the ball with the SAME linear part
# (eps, delta, k), the difference D = P - P' is a nonzero Laurent polynomial.
# A shape-specific collision for triangle (a,b) requires D(zeta_T)=0, i.e.
# (rational root thm over Z[i], zeta = mu/lambda, N(lambda)=a^2+b^2 for
# primitive a-bi): lambda | lead(D) and mu | const(D)  (after normalizing
# D to a polynomial with nonzero constant term). Hence
#   a^2+b^2  |  N(lead(D))  = lead(D)^2   (lead(D) is a rational integer!)
#   a^2+b^2  |  const(D)^2
# So min(|lead D|, |const D|)^2 >= a^2+b^2 >= 5. We histogram
# m(D) = min(|lead D|,|const D|) over ALL same-class pairs in the ball.
import sys
from collections import defaultdict
exec(open('/tmp/zeta_probe/probe.py').read().split("maxd=int")[0])

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
layers=bfs(maxd)
ball=[el for L in layers for el in L]
classes=defaultdict(list)
for el in ball:
    classes[(el[0],el[1],el[2])].append(sorted(el[3].items()))
print("ball size", len(ball), " classes", len(classes), " max class", max(len(v) for v in classes.values()))

hist=defaultdict(int); worst=[]
import itertools
for cls, polys in classes.items():
    n=len(polys)
    if n<2: continue
    # convert to dicts once
    ds=[dict(p) for p in polys]
    for i in range(n):
        Pi=ds[i]
        for j in range(i+1,n):
            D=dict(Pi)
            for e,c in ds[j].items():
                D[e]=D.get(e,0)-c
                if D[e]==0: del D[e]
            if not D: continue   # would be symbolic equality (shouldn't happen)
            es=sorted(D)
            lead=abs(D[es[-1]]); const=abs(D[es[0]])
            m=min(lead,const)
            hist[m]+=1
            if m>=3 and len(worst)<5: worst.append((cls,sorted(D.items())))
print("histogram of m(D)=min(|lead|,|const|):")
for m in sorted(hist): print(f"  m={m}: {hist[m]} pairs")
# minimal c=a^2+b^2 that could kill a pair must divide m^2 (and be >=5):
ok=[m for m in hist if m*m>=5]
print("pairs with m^2>=5 (could conceivably admit a small-triangle root):",
      sum(hist[m] for m in ok), "of", sum(hist.values()))
for w in worst[:3]: print("example large-m difference:", w)
