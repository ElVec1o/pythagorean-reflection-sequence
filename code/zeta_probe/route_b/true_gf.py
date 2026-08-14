#!/usr/bin/env python3
"""
Cycle-weighted assembly: W(x,y) where y marks each FORCED ISOLATED CYCLE.
Hypothesis (validated combinatorially in bulk_cycle_rule.py / cyc_indep_k2.py):
  each gap edge inside the span (a=0,f=0, forced crossing m=2) is an isolated 2-cycle
  in the deposited multigraph, costing +2 in the TRUE metric (splice), but free in
  relaxed. So:
    relaxed length  = (existing fast_relaxed3 sweep)          -> V = W(x,1)
    true length     = relaxed length + 2*(#gap edges in span) -> U = W(x,q), q=x^2
  We instrument the sweep: every time a gap edge (aj==0 and fj==0) is taken inside the
  span, multiply by y (one cycle). Track length-poly in x AND cycle-count via y.
  Then V_n = sum over cycle counts, U_n = shift each gap-cycle by +2 in length.

  IMPLEMENTATION: carry a 2D table  deg_in_x -> {ncyc -> count}. A gap-edge transition
  adds 2 to x-degree (the crossing) and +1 to ncyc. At the end:
     V(x):  coeff of x^n = sum_{ncyc} table[n][ncyc]
     U(x):  coeff of x^n = sum_{ncyc} table[n-2*ncyc... ] -- careful: each cycle adds +2.
            i.e. element with relaxed_len=L and ncyc=c has true_len=L+2c. So
            U_n = sum over (L,c) with L+2c=n of table[L][c].
"""
import sys
from collections import defaultdict

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

# reuse boundary_site_cost and deposits from catalytic_funceq via fast_relaxed3
import os, importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("fr3", os.path.join(HERE,"fast_relaxed3.py"))
fr3=importlib.util.module_from_spec(spec); sys.argv=["fr3","0"]; spec.loader.exec_module(fr3); sys.argv=_save
boundary_site_cost=fr3.boundary_site_cost
deposits=fr3.deposits

import c_formula as _C
shield_right=_C.shield_right; shield_left=_C.shield_left

def _cross(aj,fj):
    return 2 if (aj==0 and fj==0) else max(abs(aj),abs(fj))

# poly = dict: xdeg -> dict(ncyc -> count)
def padd(tgt, src, dx, dc):
    for d,sub in src.items():
        nd=d+dx
        t=tgt[nd]
        for nc,cnt in sub.items():
            t[nc+dc]+=cnt

def slice_gf(eps,delta,k,N,cap):
    K0=min(0,k); K1=max(0,k)
    M=N+1
    JLO=K0-M; JHI=K1+M
    out=defaultdict(lambda: defaultdict(int))   # xdeg -> {ncyc->cnt}
    if k==0:
        bc=boundary_site_cost(0,0,0,0,True,True,eps,delta)
        if bc is not None and bc<=N: out[bc][0]+=1
    def newstate(): return defaultdict(lambda: defaultdict(int))
    states={'pre':{0:{0:1}}}
    for j in range(JLO,JHI):
        fj=f_of(j,k)
        site_is0=(j==0); site_isk=(j==k)
        site_virtual=site_is0 or site_isk
        fL=f_of(j-1,k)
        ns={}
        def get(key):
            if key not in ns: ns[key]=defaultdict(lambda: defaultdict(int))
            return ns[key]
        for key,poly in states.items():
            if key=='pre':
                if fj==0 and j<K0:
                    padd(get('pre'),poly,0,0)
                if j<=K0:
                    for aj in deposits(fj,cap):
                        cross=_cross(aj,fj)
                        if site_virtual:
                            sc=boundary_site_cost(0,0,aj,fj,site_is0,site_isk,eps,delta)
                            if sc is None: continue
                        else:
                            sc=abs(aj)
                        add=cross+sc
                        # starting active edge: not a gap, no cycle
                        tgt=get(('in',aj,0))
                        padd(tgt, {d:sub for d,sub in poly.items()}, add, 0)
                    if site_virtual and fj==0 and j<=K0:
                        aj=0
                        cross=_cross(aj,fj)  # =2 (gap at virtual site though)
                        sc=boundary_site_cost(0,0,aj,fj,site_is0,site_isk,eps,delta)
                        if sc is not None:
                            add=cross+sc
                            # This runs only for k==0 (edge 0 with no left deposit): it is the
                            # RIGHT boundary run's first edge, so it carries the boundary shield
                            # (dc=1-shield_right, =1 in the unshielded eps=+1,dl=0 case) -- NOT 0.
                            dc0 = 1-shield_right(k,eps,delta,0) if j==K1 else 0
                            tgt=get(('in',aj,0))
                            padd(tgt, poly, add, dc0)
            else:
                aprev=key[1]; pend=key[2]
                cand=list(deposits(fj,cap))
                if fj==0:
                    cand=[0]+cand
                prev_was_gap = (aprev==0 and fL==0)
                for aj in cand:
                    cross=_cross(aj,fj)
                    is_gap = (aj==0 and fj==0)
                    if site_virtual:
                        sc=boundary_site_cost(aprev,fL,aj,fj,site_is0,site_isk,eps,delta)
                        if sc is None: continue
                    else:
                        sc=max(abs(aprev),abs(aj))
                    # CORRECTED connectivity. Baseline: each maximal gap-RUN gets shield 1 (inner
                    # turn-around) -> only gap edges after the first in a run cost a cycle. A
                    # marker site (j==0 or j==k) BREAKS runs. At the two spine boundaries the
                    # shield is the explicit boundary law (may be 0, not 1).
                    if site_virtual:
                        dc = 0
                        if is_gap and j==K1:                  # right boundary run, first edge
                            dc = 1 - shield_right(k,eps,delta,aprev)
                        if j==K0 and k<0 and prev_was_gap:    # left boundary run closes at spine
                            dc += 1 - shield_left(k,eps,delta,aj)
                    else:
                        dc = 1 if (is_gap and prev_was_gap) else 0
                    # 5-cell boundary correction (k=0,dl=0 only): ARM at site 0 when an even
                    # deposit is glued LEFT (aprev) with no adjacent-right even (aj==0); FIRE at
                    # the first right detour block. (couples the two sides of the marker.)
                    newpend=pend
                    if k==0 and delta==0 and j==0 and aprev!=0 and aprev%2==0 and aj==0:
                        newpend = -1 if eps==1 else (1 if aprev==2 else 0)
                    if pend!=0 and j>=1 and (not is_gap) and prev_was_gap:
                        dc += pend; newpend=0
                    add=cross+sc
                    tgt=get(('in',aj,newpend))
                    padd(tgt, poly, add, dc)
        states={kk:vv for kk,vv in ns.items() if vv}
        SR=j+1
        if SR>=K1:
            site_is0R=(SR==0); site_iskR=(SR==k); site_virtualR=site_is0R or site_iskR
            for key,poly in states.items():
                if key=='pre': continue
                aprev=key[1]
                active_right=(aprev!=0) or (fj!=0)
                if not active_right and not site_virtualR:
                    continue
                if site_virtualR:
                    sc=boundary_site_cost(aprev,fj,0,0,site_is0R,site_iskR,eps,delta)
                    if sc is None: continue
                else:
                    sc=abs(aprev)
                for d,sub in poly.items():
                    nd=d+sc
                    if nd<=N:
                        for nc,cnt in sub.items():
                            out[nd][nc]+=cnt
        if not states: break
    return out

def assemble(N, cap=None, kmax=None):
    if cap is None: cap=N//3+2
    if kmax is None: kmax=N+1
    table=defaultdict(lambda: defaultdict(int))  # xdeg(relaxed) -> {ncyc->cnt}
    for k in range(-kmax,kmax+1):
        for eps in (1,-1):
            for delta in (0,1):
                gf=slice_gf(eps,delta,k,N,cap)
                for d,sub in gf.items():
                    if d<=N:
                        for nc,cnt in sub.items():
                            table[d][nc]+=cnt
    # V_n: sum over ncyc at relaxed deg n
    V=[0]*(N+1); U=[0]*(N+1)
    for d,sub in table.items():
        for nc,cnt in sub.items():
            if d<=N: V[d]+=cnt
            t=d+2*nc
            if t<=N: U[t]+=cnt
    return V,U,table

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 20
    V,U,table=assemble(N, kmax=N//2+1)
    ref_v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490,166969,254047,386192,586349,889599,1347444,2039911,3084135,4661368,7035665,10617513,16002526,24117471,36303371,54649900,82171011]
    ref_u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]
    print("V=",V)
    print("U=",U)
    vok=all(V[n]==ref_v[n] for n in range(min(N+1,len(ref_v))))
    uok=all(U[n]==ref_u[n] for n in range(min(N+1,len(ref_u))))
    print("V matches v_n:", vok)
    print("U matches u_n:", uok)
    if not uok:
        for n in range(min(N+1,len(ref_u))):
            if U[n]!=ref_u[n]:
                print(f"  U mismatch n={n}: got {U[n]} ref {ref_u[n]} diff {U[n]-ref_u[n]}")
    if uok and N>=len(ref_u):
        print("ALL 43 OEIS terms reproduced. NEW terms (poly-time, past the BFS wall):")
        for n in range(len(ref_u),N+1):
            print(f"  u_{n} = {U[n]}")
