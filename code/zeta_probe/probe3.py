# Sharp test: a same-class difference D can vanish at an admissible zeta_T
# ONLY IF some prime p == 1 (mod 4) divides gcd(lead(D), const(D)).
# (lambda | lead, mu=conj(lambda) | const in Z[i]; N(lambda)=c odd, all
#  prime factors of c split (c primitive norm); c>=5.)
# We scan ALL same-linear-part pairs in the ball and record:
#   - histogram of g = gcd(|lead|,|const|)
#   - any pair where a prime ==1 mod 4 divides g  -> DANGEROUS
import sys, math
from collections import defaultdict
exec(open('/tmp/zeta_probe/probe.py').read().split("maxd=int")[0])

def odd14(n):  # primes ==1 mod 4 dividing n
    out=[]; m=n
    d=3
    while m%2==0: m//=2
    while d*d<=m:
        if m%d==0:
            if d%4==1: out.append(d)
            while m%d==0: m//=d
        d+=2
    if m>1 and m%4==1: out.append(m)
    return out

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 15
layers=bfs(maxd)
ball=[]
for d,L in enumerate(layers):
    for el in L: ball.append((d,el))
classes=defaultdict(list)
for d,el in ball:
    classes[(el[0],el[1],el[2])].append((d,dict(el[3])))
print("ball", len(ball), "classes", len(classes))

ghist=defaultdict(int); danger=[]
for cls, items in classes.items():
    n=len(items)
    for i in range(n):
        di,Pi=items[i]
        for j in range(i+1,n):
            dj,Pj=items[j]
            D=dict(Pi)
            for e,c in Pj.items():
                D[e]=D.get(e,0)-c
                if D[e]==0: del D[e]
            es=sorted(D)
            g=math.gcd(abs(D[es[-1]]), abs(D[es[0]]))
            ghist[g]+=1
            bad=odd14(g)
            if bad: danger.append((cls,di,dj,sorted(D.items()),bad))
print("gcd(lead,const) histogram:", dict(sorted(ghist.items())))
print("DANGEROUS pairs (prime==1 mod 4 divides both extremes):", len(danger))
for x in danger[:5]: print("  ", x)
