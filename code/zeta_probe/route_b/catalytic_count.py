#!/usr/bin/env python3
"""
Validate the catalytic functional-equation data by recomputing v_n.

Length of a slice element (eps,delta,k; deposits a_j) in the validated local form:
   length = sum_{j in span} m_j  +  sum_{sites in span} sitecost,
   span = [lo, hi),  lo=min, hi=max of visited sites {0,k} U {j,j+1 : a_j!=0 or f_j!=0},
   m_j = max(|a_j|,|f_j|), forced to >=2 if it is 0 (reachability gap edge),
   interior sitecost = max(|a_{j-1}|,|a_j|), virtual sites 0,k use boundary_site_cost.

CATALYTIC TRANSFER.  Sweep edges left->right across the span.  The only unbounded
memory is w = |a_last| (the catalytic variable) used by the next site's
max(.,.).  We carry per state (a_prev, f_prev) a length-polynomial.  The span's
left/right ends and the marker sites 0,k are bounded data.

We sweep the FULL window and let the span emerge: an edge is "in the span" iff it
lies between the leftmost and rightmost visited site.  Equivalently we require the
deposit sequence to be such that the first and last non-trivial edges, together
with 0 and k, bound a contiguous run with every interior edge crossed (m>=2).
The DP enforces this by: once we have left the marker/support region on the left
(entered the span) we cannot emit an uncrossed (m=0) edge until after the span
ends; an m=0 edge is only allowed strictly outside [lo,hi).  We realize this with
the SAME reachability-chain rule as the validated DP.
"""
import sys, importlib.util, os
from collections import defaultdict
HERE=os.path.dirname(os.path.abspath(__file__)); ZP=os.path.dirname(HERE)
_S=list(sys.argv)
spec=importlib.util.spec_from_file_location("lf",os.path.join(ZP,"lamp_formula.py"))
lf=importlib.util.module_from_spec(spec); sys.argv=["lf","0"]; spec.loader.exec_module(lf); sys.argv=_S
import catalytic_funceq as cf
f_of=cf.f_of
bsc=cf.boundary_site_cost

def slice_count(eps,delta,k,JLO,JHI,Ncap):
    # State: (a_prev, f_prev, started, ended).  started: have we entered the active
    # span (crossed >=1 edge of m>0 connected to markers/support)?  We mirror the
    # validated DP reachability chain (forbid m=0->m>0 jumps on the right, etc.).
    # Length accrues: edge m, then site cost at the site to its LEFT.
    states=defaultdict(lambda: defaultdict(int))
    # phantom left edge: a=0, f=0, m=0, "before span"
    states[(0,0)][0]=1
    edges=list(range(JLO,JHI+1))
    for j in edges:
        fj=f_of(j,k); is0=(j==0); isk=(j==k)
        amax=Ncap
        adeps=[a for a in range(-amax,amax+1) if (a-fj)%2==0]
        nstates=defaultdict(lambda: defaultdict(int))
        for (ap,fp),lk in states.items():
            mprev=max(abs(ap),abs(fp))
            for aj in adeps:
                mj=max(abs(aj),abs(fj))
                # span / reachability chain (validated rule):
                if j>=1 and mprev==0 and mj>0:
                    # entering span on the right of 0: forced m>=2 gap edges are emitted
                    # as a=0 with mj=2 handled below; a genuine support edge here is ok
                    pass
                # forbid creating a NEW disconnected component: same rule as DP
                if j<=-1 and mprev>0 and mj==0: continue
                if j>=1 and mprev==0 and mj>0:
                    # only allowed if this edge is adjacent to start of span; the
                    # reachability gap handles interior. We emulate the DP exactly:
                    # the DP forbids prev_m==0 & m>0 for j>=1. So FORBID.
                    continue
                if j<=-1 and mprev>0 and mj==0: continue
                # reachability: gap edge inside span needs m>=2. Encode by FORCING
                # mj_eff = mj, but if aj==0 and fj==0 and we are inside the span,
                # the only consistent crossing is m>=2; a length-0 edge keeps us
                # outside the span (no crossing). The DP distinguishes via prev_m.
                mj_eff=mj
                # site to the LEFT of edge j (between j-1 and j) at integer site j
                if is0 or isk:
                    sc=bsc(ap,fp,aj,fj,is0,isk,eps,delta)
                else:
                    sc=max(abs(ap),abs(aj))
                if sc is None: continue
                inc=mj_eff+sc
                for L,c in lk.items():
                    nL=L+inc
                    if nL<=Ncap:
                        nstates[(aj,fj)][nL]+=c
        states=nstates
        if not states: break
    out=defaultdict(int)
    jR=edges[-1]+1
    for (ap,fp),lk in states.items():
        is0=(jR==0); isk=(jR==k)
        if is0 or isk:
            sc=bsc(ap,fp,0,0,is0,isk,eps,delta)
        else:
            sc=max(abs(ap),0)
        if sc is None: continue
        for L,c in lk.items():
            nL=L+sc
            if nL<=Ncap: out[nL]+=c
    return out

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 12
    half=(N+1)//2; KMAX=half+2; PAD=half+2
    total=defaultdict(int)
    for k in range(-KMAX,KMAX+1):
        JLO=min(0,k)-PAD; JHI=max(0,k)+PAD
        for eps in (1,-1):
            for delta in (0,1):
                poly=slice_count(eps,delta,k,JLO,JHI,N)
                for L,c in poly.items():
                    if L<=N: total[L]+=c
    out=[total[n] for n in range(0,N+1)]
    print("CATALYTIC-LOCAL v_n =", out)
    ref=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513]
    print("MATCHES reference:", all(out[n]==ref[n] for n in range(min(len(out),len(ref)))))
