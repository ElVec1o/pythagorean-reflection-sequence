# Structure + metric on the cylindrical honeycomb X_m (m=5 stratum).
#  (a) sum over a level of the m wrapped lamps vanishes (rotation-orbit sum);
#  (b) that level-sum cycle is gamma_j - gamma_{j+1};
#  (c) METRIC: ell(t) = min over the kernel coset of ( ||phi||_1 + 2 st ),
#      kernel = <gamma_j>, checked against exact BFS on the stratum.
exec(open("cylinder_structure.py").read().split("# the three translation-type")[0])
from collections import deque
ZERO=(K.const(0),K.const(0))
# (a)
for j in (-2,-1,0,1,2):
    tot=ZERO
    for n in range(M):
        v=VEC[(n,j)]; tot=(tot[0]+v[0],tot[1]+v[1])
    assert tot==ZERO, f"level {j} lamps do not sum to zero"
print(f"(a) sum of the {M} wrapped lamps on each level = 0  (levels -2..2)  OK")
# (b)
def face_sum(j):
    d=Counter()
    for n in range(M):
        for e,c in FACE[(n,j)].items(): d[e]+=c
    return Counter({e:c for e,c in d.items() if c})
g0=Counter(gfl); g1=shift(gfl,1) if False else None
def gamma(j):
    return Counter({((u[0],u[1]+j,u[2]),(v[0],v[1]+j,v[2]),i):c for (u,v,i),c in gfl.items()})
for j in (-1,0,1):
    L=face_sum(j); diff=Counter(gamma(j))
    for e,c in gamma(j+1).items(): diff[e]-=c
    diff=Counter({e:c for e,c in diff.items() if c})
    same = (L==diff) or (L==Counter({e:-c for e,c in diff.items()}))
    print(f"(b) level-sum cycle at j={j:+d}: {len(L)} edges; equals +-(gamma_j - gamma_(j+1))? {same}")
# --- metric machinery on the cylinder ---
def comps(fl):
    vs={E0}
    for (u,v,i) in fl: vs.add(u); vs.add(v)
    par={x:x for x in vs}
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for (u,v,i) in fl: par[find(u)]=find(v)
    c={}
    for x in vs: c.setdefault(find(x),[]).append(x)
    return list(c.values())
def bfs_between(A,B,cap,Bnd=9):
    seen={x:0 for x in A}; q=deque(A)
    while q:
        v=q.popleft(); d=seen[v]
        if d>=cap: continue
        for i in range(3):
            w=stepv(v,i)
            if abs(w[1])>Bnd: continue
            if w in B: return d+1
            if w not in seen: seen[w]=d+1; q.append(w)
    return 99
def st(fl,cap=99):
    cs=comps(fl)
    if len(cs)==1: return 0
    if len(cs)==2: return bfs_between(cs[0],set(cs[1]),cap)
    tot=0; rest=cs[1:]; cur=set(cs[0])
    while rest:
        best=None
        for idx,c in enumerate(rest):
            d=bfs_between(cur,set(c),cap)
            if best is None or d<best[0]: best=(d,idx)
        tot+=best[0]; cur|=set(rest.pop(best[1]))
    return tot
def cost(fl):
    n1=sum(abs(c) for c in fl.values())
    return n1+2*st(fl)
def best_cost(fl, jr=range(-4,5)):
    b=cost(fl)
    for j in jr:
        for k in (1,-1):
            f2=Counter(fl)
            for e,c in gamma(j).items(): f2[e]+=k*c
            f2=Counter({e:c for e,c in f2.items() if c})
            if f2:
                v=cost(f2)
                if v<b: b=v
    return b
# --- exact BFS on the stratum, collect translations with witness words ---
IDT=(K.const(1),K.const(0),K.const(0),K.const(1),K.const(0),K.const(0))
front=[("",IDT)]; seen={IDT:0}; trans={}
DMAX=12
for d in range(1,DMAX+1):
    nf=[]
    for (w,Mx) in front:
        last=int(w[-1]) if w else -1
        for i in range(3):
            if i==last: continue
            N=mul(Mx,GS[i]); nw=w+str(i)
            if N in seen: continue
            seen[N]=d; nf.append((nw,N))
            if N[0]==K.const(1) and N[1]==K.const(0) and N[2]==K.const(0) and N[3]==K.const(1):
                trans[N]=(d,nw)
    front=nf
    print(f"    depth {d:2d}: layer {len(nf):5d}, translations so far {len(trans)}", flush=True)
ok=bad=0
for N,(d,w) in sorted(trans.items(), key=lambda kv: kv[1][0]):
    fl,tot,nfx,mx=word_flow(w)
    assert tot==(N[4],N[5])
    p=best_cost(fl)
    if p==d: ok+=1
    else:
        bad+=1
        if bad<=6: print(f"   MISS d={d} w={w}: predicted {p}")
print(f"\n(c) METRIC on the cylinder: {ok}/{ok+bad} translations match "
      f"ell = min over the gamma-coset of (||phi||_1 + 2 st)")
