#!/usr/bin/env python3
"""
EXACT cycle-weighted GF.  We compute, per element, c(g) EXACTLY via:
    c(g) = (# gap edges in span)  -  shield(0)  -  shield(k)
where shield(m) in {0,1,2} is the number of gap edges that the marker at site m connects
to the spine for free.  We DON'T hand-derive shield; instead we compute c(g) exactly as
(true_len - relaxed_len)/2 from the validated solvers, then BIN by (relaxed_len, c) to
build W(x,y), and finally form U=W(x,q).  This is exact by construction; its purpose is to
(a) confirm the cycle interpretation reproduces u_n to high order, and
(b) expose c's distribution (bounded boundary correction + interior count).
Uses the fast closed-form relaxed_len and BFS true distance => O(elements) and fast.
"""
import sys, os
from collections import defaultdict
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def build(N):
    RAD=N+ N//2 + 12   # true_len can exceed relaxed by 2c; c<= (#gap edges) ~ span; generous
    dist=LL.bfs(RAD)
    # W: relaxed_deg -> {c -> count}
    W=defaultdict(lambda: defaultdict(int))
    for (e,dl,k,L),tl in dist.items():
        rl=relaxed_len(e,dl,k,L)
        if rl is None or rl>RAD: continue
        if rl>tl:  # shouldn't happen
            continue
        c=(tl-rl)//2
        W[rl][c]+=1
    # But BFS to RAD may MISS elements whose relaxed_len<=N but true_len>RAD. Check coverage:
    # an element with relaxed_len=L has true_len=L+2c. We need it captured => L+2c<=RAD.
    # c can be as large as ~ (#gap edges). For relaxed_len<=N, the span is <=~N/2, so c<=N/2,
    # true_len<= N+N = 2N. Set RAD>=2N to be safe. Recompute with that.
    return W

def build_safe(N):
    RAD=2*N+4
    dist=LL.bfs(RAD)
    W=defaultdict(lambda: defaultdict(int))
    for (e,dl,k,L),tl in dist.items():
        rl=relaxed_len(e,dl,k,L)
        if rl is None or rl>N: continue
        c=(tl-rl)//2
        W[rl][c]+=1
    return W

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 18
    W=build_safe(N)
    V=[0]*(N+1); U=[0]*(N+1)
    for rl,sub in W.items():
        for c,cnt in sub.items():
            if rl<=N: V[rl]+=cnt
            t=rl+2*c
            if t<=N: U[t]+=cnt
    ref_v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490]
    ref_u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,62263,94622]
    print("V=",V)
    print("U=",U)
    print("V OK:", all(V[n]==ref_v[n] for n in range(min(N+1,len(ref_v)))))
    print("U OK:", all(U[n]==ref_u[n] for n in range(min(N+1,len(ref_u)))))
    # cycle-count distribution by relaxed length (shows boundary boundedness)
    print("\nc-distribution at each relaxed_len:")
    for rl in range(8, min(N+1,16)):
        print(f"  rl={rl}: {dict(sorted(W[rl].items()))}")
