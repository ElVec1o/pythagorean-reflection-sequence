import itertools, sys
def involutions(n):
    # perfect matchings on range(n) as fixed-point-free involutions
    pts=list(range(n))
    def rec(rem):
        if not rem: yield {}
        else:
            a=rem[0]
            for i in range(1,len(rem)):
                b=rem[i]
                for r in rec(rem[1:i]+rem[i+1:]):
                    r=dict(r); r[a]=b; r[b]=a; yield r
    yield from rec(pts)
bad=0; tot=0
for n in [4,6,8]:
    invs=list(involutions(n))
    for p in invs:
        for t in invs:
            if any(p[x]==t[x] for x in range(n)): continue   # pt_ne
            tot+=1
            sig=lambda x: t[p[x]]
            for a in range(n):
                orb=[]; y=a
                while True:
                    orb.append(y); y=sig(y)
                    if y==a: break
                if p[a] in orb:
                    bad+=1
                    print("COUNTEREXAMPLE n=%d a=%d p=%s t=%s orb=%s"%(n,a,p,t,orb)); sys.exit()
print("valid (p,t) pairs checked:",tot,"  violations:",bad)
