# Step 1: BFS the lamp model storing exact distances; Step 2: compute the
# "base cost" (forced h-moves) and examine the excess chi = dist - base.
import sys
from collections import defaultdict

def freeze(d): return tuple(sorted(d.items()))

def bfs(maxd):
    ident=(1,0,0,())
    dist={ident:0}; frontier=[ident]
    for d in range(maxd):
        nxt=[]
        for (e,dl,k,L) in frontier:
            cands=[(e,1-dl,k,L), (-e,1-dl,k,L)]
            D=dict(L)
            if dl==0:
                D[k-1]=D.get(k-1,0)+e
                if D[k-1]==0: del D[k-1]
                cands.append((e,1,k-1,freeze(D)))
            else:
                D=dict(L); D[k]=D.get(k,0)-e
                if D[k]==0: del D[k]
                cands.append((e,0,k+1,freeze(D)))
            for ne in cands:
                if ne not in dist:
                    dist[ne]=d+1; nxt.append(ne)
        frontier=nxt
    return dist

def base_moves(k,L):
    a=dict(L)
    edges=set(a)
    # travel edges: between 0 and k
    if k>0: tr=set(range(0,k))
    elif k<0: tr=set(range(k,0))
    else: tr=set()
    act = edges|tr
    if not act: return 0,0,0
    A,B=min(act),max(act)
    M=0; forced0=0
    for j in range(A,B+1):
        v=abs(a.get(j,0))
        if v==0: M+=2; forced0+=1
        else: M+=v
    return M,A,B

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
dist=bfs(maxd)
# histogram of chi by simple features
hist=defaultdict(int)
samples=defaultdict(list)
for (e,dl,k,L),d in dist.items():
    M,A,B=base_moves(k,L)
    chi=d-M
    # features: k, eps, delta, #signchanges in the sequence of nonzero a_j signs
    a=dict(L)
    if a:
        idxs=sorted(a)
        sgns=[1 if a[j]>0 else -1 for j in idxs]
        flips=sum(1 for i in range(1,len(sgns)) if sgns[i]!=sgns[i-1])
    else:
        flips=0
    key=(k,e,dl,flips)
    hist[(chi,)+key]+=1
    if len(samples[(chi,)+key])<2: samples[(chi,)+key].append((k,e,dl,dict(L),d,M))
print("chi distribution (chi, k, eps, delta, signflips) -> count   [ball depth", maxd, "]")
for kk in sorted(hist):
    print(f"  chi={kk[0]:2d} k={kk[1]:3d} eps={kk[2]:2d} dl={kk[3]} flips={kk[4]}: {hist[kk]}")
