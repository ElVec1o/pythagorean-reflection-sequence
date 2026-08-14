#!/usr/bin/env python3
"""
Derive & TEST the cycle-weighted BULK-run recursion, to determine whether the
cycle-corrected bulk dressing B_U shares the relaxed bulk denominator (1 - S_1).

Relaxed bulk section identity (q=x^2; bulk edge half-magnitude s>=1, weight 2):
  F_s = 2q^s + 2q^s sum_{s'>=s} F_{s'} q^{s'} + 2q^{2s} sum_{s'<s} F_{s'}.
Telescoping (G_k=F(q,q^k)=sum_s F_s q^{ks}):
  G_k = alpha_k (1+G_1) + gamma_k G_{k+2},
  alpha_k = 2q^{k+1}/(1-q^{k+1}), gamma_k = 2q^{k+2}/(1-q^{k+2}) - 2q^{k+1}/(1-q^{k+1}).
  G_0 = S_0/(1-S_1).

GAP EDGES & CYCLES. Inside a bulk run we may also place GAP edges (a=0, forced m=2,
length 2 => factor q). The cycle rule (bulk_cycle_rule.py, cyc_indep_k2.py): a gap
edge separating the run from the next deposit creates ONE isolated cycle (cost +2 in
true = factor q in q-grading), and this is magnitude- & k-independent. So in the
TRUE grading each gap edge carries weight q (its length) TIMES y (cycle marker, set
y=q for true since +2 => q^1, y=1 for relaxed).

Hypothesis to TEST: inserting gap edges multiplies the run by a GEOMETRIC factor in
(q^2 y) [length 2 + cycle weight], i.e. a factor 1/(1 - q^2 y) or similar, which is
ANALYTIC and does NOT change the denominator 1-S_1. Then:
   B_V = S_0/(1-S_1) * 1/(1-q^2)          [relaxed: gap edges free-cycle, y=1... but
                                            wait relaxed gap edge still costs its
                                            length q^2? NO: in relaxed the gap edge
                                            length is 2 (factor q) and cycle FREE.]
We TEST against the actual cycle-weighted bulk series from a brute bulk enumeration.
"""
import sys, os, importlib.util
from collections import defaultdict
import mpmath as mp
mp.mp.dps=30

HERE=os.path.dirname(os.path.abspath(__file__))
import lamp_lib as LL
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf)
relaxed_len=cf.relaxed_len_local

def bulk_cycle_series(Lmax=9, Smax=6, side='right'):
    """Enumerate pure-bulk runs at k=0, eps=1, dl=0, deposits on edges 0..L-1 (right)
       each in {0(gap), +-2,+-4,..,+-2Smax}. For each, compute relaxed_len rl and
       cycle count c=(tl-rl)/2 (tl from validated LL.solve). Bin by (rl, c).
       Return W_bulk[(rl,c)] = count. This is the cycle-weighted bulk GF building block."""
    from itertools import product
    W=defaultdict(int)
    evens=[0]+[s for m in range(1,Smax+1) for s in (2*m,-2*m)]
    for L in range(0,Lmax+1):
        for combo in product(evens, repeat=L):
            # right run: edges 0..L-1
            a={i:combo[i] for i in range(L) if combo[i]!=0}
            rl=relaxed_len(1,0,0,a); tl=LL.solve(1,0,0,a)
            if rl is None or tl is None: continue
            c=(tl-rl)//2
            W[(rl,c)]+=1
    return W

if __name__=="__main__":
    Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 7
    Smax=int(sys.argv[2]) if len(sys.argv)>2 else 4
    W=bulk_cycle_series(Lmax,Smax)
    # Build bivariate: relaxed series V_b(q) = sum_{rl,c} W[rl,c] q^{rl/?}  (rl is in x, q=x^2)
    # and true U_b(q) where each cycle adds +2 to length: x^{rl+2c}.
    # Express in q=x^2: rl,2c are even? bulk lengths are even -> yes.
    Vb=defaultdict(int); Ub=defaultdict(int)
    for (rl,c),cnt in W.items():
        Vb[rl]+=cnt
        Ub[rl+2*c]+=cnt
    maxd=2*Lmax+8
    print("bulk relaxed V_b coeffs (by x-deg):", [Vb.get(n,0) for n in range(0,maxd,2)])
    print("bulk true    U_b coeffs (by x-deg):", [Ub.get(n,0) for n in range(0,maxd,2)])
    # cycle distribution
    cdist=defaultdict(int)
    for (rl,c),cnt in W.items(): cdist[c]+=cnt
    print("cycle count distribution over bulk runs:", dict(sorted(cdist.items())))
    # KEY: ratio of U_b to V_b coefficients -- if cycles just shift, the SINGULARITY
    # of U_b should be >= that of V_b (cycles add length => slower growth => larger radius)
    vb=[Vb.get(n,0) for n in range(0,maxd,2)]
    ub=[Ub.get(n,0) for n in range(0,maxd,2)]
    print("\nratio U_b[n]/V_b[n] (cycle-correction is a CONTRACTION if <=1 and ->):")
    for i in range(2,min(len(vb),len(ub))):
        if vb[i]>0:
            print(f"  n(q)={i}: V_b={vb[i]} U_b={ub[i]} ratio={ub[i]/vb[i]:.4f}")
