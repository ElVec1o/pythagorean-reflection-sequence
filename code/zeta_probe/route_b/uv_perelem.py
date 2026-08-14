#!/usr/bin/env python3
# Per-element (relaxed_len, true_len) census. relaxed via validated relaxed_len_local
# (Lemma D), true via BFS. Build u_n, v_n, d_n. Test the +2-per-cycle law:
# true_len - relaxed_len is even and >= 0; report the joint distribution and the
# "cycle number" c = (true-relaxed)/2 per element.
import sys, importlib.util, os
from collections import Counter, defaultdict

HERE=os.path.dirname(os.path.abspath(__file__)); ZP=os.path.dirname(HERE)
spec=importlib.util.spec_from_file_location("cf",os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); _S=list(sys.argv); sys.argv=["cf","0"]
spec.loader.exec_module(cf); sys.argv=_S
relaxed_len_local=cf.relaxed_len_local
lf=cf.lf

def main(R):
    dist=lf.bfs(R)             # element -> true length
    u=Counter(); v=Counter()
    # joint: for each element, (true, relaxed); cycles = (true-relaxed)//2
    joint=Counter()            # (true,c) -> count
    odd=0; neg=0
    # We only TRUST true length up to elements whose true length <= R (BFS converged
    # for those). Same for relaxed (relaxed<=true<=R).
    for (e,dl,k,Lp),tl in dist.items():
        if tl> R: continue
        rl=relaxed_len_local(e,dl,k,Lp)
        if rl is None: continue
        diff=tl-rl
        if diff<0: neg+=1; continue
        if diff%2: odd+=1
        c=diff//2
        u[tl]+=1
        v[rl]+=1
        joint[(tl,c)]+=1
    print("odd diffs:",odd,"neg diffs:",neg)
    U=[u.get(n,0) for n in range(R+1)]
    V=[v.get(n,0) for n in range(R+1)]
    D=[V[n]-U[n] for n in range(R+1)]
    print("u_n=",U)
    print("v_n=",V)
    print("d_n=",D)
    # cycle-number distribution among elements of true length n
    print("\n# elements of true length n with c isolated cycles (c=0,1,2,...):")
    maxc=max((c for (tl,c) in joint), default=0)
    for n in range(R+1):
        row=[joint.get((n,c),0) for c in range(maxc+1)]
        if sum(row)>0:
            print(f"  n={n}: {row}")
    return U,V,D,joint

if __name__=="__main__":
    R=int(sys.argv[1]) if len(sys.argv)>1 else 12
    main(R)
