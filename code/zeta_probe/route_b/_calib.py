import lamp_lib as LL
from collections import defaultdict
dist=LL.bfs(15)   # depth 15
# u_n
u=defaultdict(int)
for el,d in dist.items(): u[d]+=1
print("u_0..u_15 (BFS):", [u[n] for n in range(16)])
# verify solve matches BFS distance, and find bounds: max|k|, support span, max|value| by distance
maxk=defaultdict(int); maxval=defaultdict(int); maxspan=defaultdict(int); maxsupp=defaultdict(int)
mism=0
for (e,dl,k,L),d in dist.items():
    sl=LL.solve(e,dl,k,dict(L))
    if sl!=d: mism+=1
    maxk[d]=max(maxk[d],abs(k))
    if L:
        sites=[s for s,v in L]
        maxspan[d]=max(maxspan[d], max(sites)-min(sites))
        maxval[d]=max(maxval[d], max(abs(v) for s,v in L))
        maxsupp[d]=max(maxsupp[d], len(L))
print("solve==BFS mismatches:",mism,"of",len(dist))
print("max|k| by d:    ",[maxk[n] for n in range(16)])
print("max span by d:  ",[maxspan[n] for n in range(16)])
print("max|value| by d:",[maxval[n] for n in range(16)])
print("max|support| by d:",[maxsupp[n] for n in range(16)])
# relaxed_solve sanity: relaxed <= true
rl_ok=all(LL.relaxed_solve(e,dl,k,dict(L))<=LL.solve(e,dl,k,dict(L)) for (e,dl,k,L) in list(dist)[:2000])
print("relaxed<=true (sample):",rl_ok)
