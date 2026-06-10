# (a) Is every same-class difference divisible by t-1 (i.e., D(1)=0)?
#     Test: is P(1) a class invariant?
# (b) Same for t+1 (D(-1)=0)?
# (c) Exact kill of dangerous pairs: evaluate D at zeta for all candidate
#     small triangles (c | gcd^2): here only c=5 -> (a,b)=(1,2),(2,1)... zeta=(-3+4i)/5 or conj.
import sys
from collections import defaultdict
from fractions import Fraction
exec(open('/tmp/zeta_probe/probe.py').read().split("maxd=int")[0])

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 16
layers=bfs(maxd)
classes=defaultdict(list)
for d,L in enumerate(layers):
    for el in L: classes[(el[0],el[1],el[2])].append(dict(el[3]))

inv1=True; invm1=True
for cls, items in classes.items():
    v1 = {sum(P.values()) for P in items}                       # P(1)
    vm1 = {sum(c*(-1)**(e%2) for e,c in P.items()) for P in items}  # P(-1)
    if len(v1)>1: inv1=False
    if len(vm1)>1: invm1=False
print(f"P(1) constant within every class (=> (t-1) | every difference): {inv1}")
print(f"P(-1) constant within every class (=> (t+1) | every difference): {invm1}")

# evaluate at zeta=(-3+4i)/5 exactly using Fractions (Gaussian rational)
def evalz(D, zr, zi):
    # compute sum c*z^e ; z^e via repeated mult on Fractions
    # build power cache for needed range
    es=sorted(D)
    lo,hi=es[0],es[-1]
    pw={0:(Fraction(1),Fraction(0))}
    def mul(p,q): return (p[0]*q[0]-p[1]*q[1], p[0]*q[1]+p[1]*q[0])
    z=(zr,zi); zinv=(zr/(zr*zr+zi*zi), -zi/(zr*zr+zi*zi))
    cur=(Fraction(1),Fraction(0))
    for e in range(1,hi+1):
        cur=mul(cur,z); pw[e]=cur
    cur=(Fraction(1),Fraction(0))
    for e in range(1,-lo+1):
        cur=mul(cur,zinv); pw[-e]=cur
    tot=(Fraction(0),Fraction(0))
    for e,c in D.items():
        tot=(tot[0]+c*pw[e][0], tot[1]+c*pw[e][1])
    return tot

# re-find dangerous pairs and exact-check them
import math
def odd14(n):
    out=[]; m=n
    while m%2==0: m//=2
    d=3
    while d*d<=m:
        if m%d==0:
            if d%4==1: out.append(d)
            while m%d==0: m//=d
        d+=2
    if m>1 and m%4==1: out.append(m)
    return out

zcands=[(Fraction(-3,5),Fraction(4,5)),(Fraction(-3,5),Fraction(-4,5)),
        (Fraction(3,5),Fraction(4,5)),(Fraction(3,5),Fraction(-4,5))]
ndanger=0; nkilled=0; alive=[]
for cls, items in classes.items():
    n=len(items)
    for i in range(n):
        for j in range(i+1,n):
            D=dict(items[i])
            for e,c in items[j].items():
                D[e]=D.get(e,0)-c
                if D[e]==0: del D[e]
            es=sorted(D)
            g=math.gcd(abs(D[es[-1]]),abs(D[es[0]]))
            bad=odd14(g)
            if not bad: continue
            ndanger+=1
            dead=True
            for zr,zi in zcands:
                v=evalz(D,zr,zi)
                if v==(0,0): dead=False; alive.append((cls,sorted(D.items()),(zr,zi)))
            if dead: nkilled+=1
print(f"dangerous pairs: {ndanger}, killed by exact evaluation: {nkilled}, ALIVE: {len(alive)}")
for a in alive[:5]: print("  ALIVE:",a)
