# Locate the elements g with c(g)>=1 (true_len > relaxed_len) at small length,
# and describe their (eps,delta,k;a) encoding to understand WHERE cycles live.
import sys
sys.path.insert(0,'/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe')
from lamp_profile import solve as true_solve, bfs
from cycle_bivariate import relaxed_solve
from collections import defaultdict

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
dist=bfs(maxd)
cyc=[]
for (e,dl,k,L),d in dist.items():
    tl=true_solve(e,dl,k,L)
    rl=relaxed_solve(e,dl,k,L)
    if tl is None or rl is None: continue
    if tl>rl:
        c=(tl-rl)//2
        cyc.append((rl,tl,c,e,dl,k,dict(L)))
cyc.sort()
print(f"# elements with c>=1, up to relaxed_len {maxd}: {len(cyc)}")
for rl,tl,c,e,dl,k,L in cyc[:40]:
    # describe: k, lamp support
    supp=sorted(L.keys())
    print(f"rl={rl} tl={tl} c={c} | eps={e} dl={dl} k={k} a={L}")
# how does c distribute?
from collections import Counter
cc=Counter(x[2] for x in cyc)
print("c distribution:", dict(cc))
# relaxed-length distribution of cycle elements
rd=Counter(x[0] for x in cyc)
print("relaxed_len of cycle elements:", dict(sorted(rd.items())))
