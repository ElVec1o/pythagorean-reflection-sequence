#!/usr/bin/env python3
"""
Compare the BULK-run GF in the RELAXED and TRUE gradings to determine whether the
cycle correction preserves the bulk denominator (1 - S_1) and only contracts (pushes
singularities outward), via a clean linear-run brute force.

We enumerate a one-sided bulk run: edges 1,2,...,L (to the RIGHT of a fixed anchor
that supplies the left connection to the trunk, so the leftmost edge is connected and
no spurious boundary cost). Concretely we model a run as a deposit pattern on a path
of edges where the FIRST edge attaches to the trunk (a connected boundary), and read:
   length(run) = sum_j m_j + sum_{interior sites} max(|a_{j-1}|,|a_j|)
with m_j = max(|a_j|, [gap->2]).  Cycle count c(run) = number of isolated 2-cycles =
(by the validated rule) the number of gap edges that are NOT bridges between two
deposits, i.e. trailing/leading gap-runs minus 1 per maximal interior gap-run... we
DON'T assume the rule; we get c from the validated connectivity DP on the run as a
k=0 right-run anchored at site 0.

Output: V_b(q) = sum_run q^{len/2}, U_b(q) = sum_run q^{(len+2c)/2}, to order Q.
Then estimate the radius of convergence of each (root test) and confirm
   rad(U_b) >= rad(V_b)   (cycle correction is a contraction; pushes pole outward).
Also: do V_b and U_b share the SAME dominant singularity location, or does U_b's move?
"""
import sys, os, importlib.util
from collections import defaultdict
from itertools import product
import mpmath as mp
mp.mp.dps=30

HERE=os.path.dirname(os.path.abspath(__file__))
import lamp_lib as LL
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf)
relaxed_len=cf.relaxed_len_local

def run_data(Lmax, Smax):
    """Right bulk run at k=0,eps=1,dl=0: deposits on edges 0..L-1.
       Record (relaxed_len, cyclecount) per config. We FILTER to runs whose first
       (leftmost) deposit is at edge 0 (anchored to marker site 0) to model a
       trunk-attached run without leading-gap inflation."""
    data=defaultdict(int)
    evens=[s for m in range(1,Smax+1) for s in (2*m,-2*m)]
    choices=[0]+evens
    for L in range(1,Lmax+1):
        for combo in product(choices, repeat=L):
            if combo[0]==0: continue   # anchor at edge 0
            a={i:combo[i] for i in range(L) if combo[i]!=0}
            rl=relaxed_len(1,0,0,a); tl=LL.solve(1,0,0,a)
            if rl is None or tl is None: continue
            c=(tl-rl)//2
            data[(rl,c)]+=1
    return data

def radius_root_test(coeffs):
    """estimate radius via limsup |c_n|^{1/n}; return 1/that."""
    vals=[]
    for n in range(2,len(coeffs)):
        if coeffs[n]>0:
            vals.append(mp.mpf(coeffs[n])**(mp.mpf(1)/n))
    if not vals: return None
    g=vals[-1]
    return 1/g if g>0 else None

if __name__=="__main__":
    Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 8
    Smax=int(sys.argv[2]) if len(sys.argv)>2 else 5
    data=run_data(Lmax,Smax)
    Q=2*Lmax+10
    Vb=defaultdict(int); Ub=defaultdict(int)
    for (rl,c),cnt in data.items():
        Vb[rl//2 if rl%2==0 else None]+=cnt if rl%2==0 else 0
        # bulk lengths even; index by q-power=rl/2
        if rl%2==0: Vb[rl//2]+=cnt
        t=rl+2*c
        if t%2==0: Ub[t//2]+=cnt
    # rebuild clean (the above double-added; redo)
    Vb=defaultdict(int); Ub=defaultdict(int)
    for (rl,c),cnt in data.items():
        if rl%2==0: Vb[rl//2]+=cnt
        t=rl+2*c
        if t%2==0: Ub[t//2]+=cnt
    vb=[Vb.get(n,0) for n in range(Q)]
    ub=[Ub.get(n,0) for n in range(Q)]
    print("V_b (q-coeffs):", vb[:Lmax+4])
    print("U_b (q-coeffs):", ub[:Lmax+4])
    cdist=defaultdict(int)
    for (rl,c),cnt in data.items(): cdist[c]+=cnt
    print("cycle distribution:", dict(sorted(cdist.items())))
    rv=radius_root_test(vb); ru=radius_root_test(ub)
    print(f"\nrad(V_b)~{mp.nstr(rv,6) if rv else None}  rad(U_b)~{mp.nstr(ru,6) if ru else None}")
    print("(bulk pole q_b=0.6096; rad(U_b)>=rad(V_b) means cycles push singularity OUT)")
    # ratio sequence
    print("ratio U_b[n]/V_b[n]:")
    for n in range(2, min(Lmax+4,len(vb))):
        if vb[n]>0: print(f"  n={n}: V={vb[n]} U={ub[n]} ratio={ub[n]/vb[n]:.4f}")
