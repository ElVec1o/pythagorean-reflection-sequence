#!/usr/bin/env python3
"""
ROUTE A -- FAST relaxed growth sequence v_n for A396406, via the validated
closed-form (Lemma D) local relaxed length.  No determinization, no profile
enumeration: the only state is the catalytic variable w = |a_prev|.

VALIDATED CLOSED FORM (this file checks it; see fast_relaxed_validate.py):
  Feasibility: for every edge j in the active span, a_j == f_j (mod 2)
               (travel edges f=+-1 need ODD deposit, bulk edges f=0 need EVEN).
  Relaxed length = sum_{j in span} max(|a_j|,|f_j|)          [gap edges -> 2]
                 + sum_{interior sites} max(|a_{j-1}|,|a_j|)
                 + boundary_site_cost at the two virtual sites 0 and k.
  span = [lo,hi) edges / [lo,hi] sites, lo=min, hi=max of VISITED sites
         = {0,k} U {j,j+1 : a_j!=0 or f_j!=0}.
  f_j = +1 on [0,k), -1 on [k,0), else 0.

This matches lamp_formula.formula_len (the BFS-validated relaxed length) on ALL
feasible configs (verified 5444/5444 exhaustively; 0/347644 feasibility errors).

DP STRUCTURE (per slice eps,delta,k)
====================================
We sweep edges left to right.  The active span has a leftmost edge `lo` whose
LEFT site `lo` is a (possibly virtual) boundary, and a rightmost edge `hi-1`
whose RIGHT site `hi` is a (possibly virtual) boundary.  The two virtual sites
are 0 and k.  Strategy: enumerate where the span starts (the left boundary site
SL) and ends (right boundary site SR), with SL<=min(0,k) and SR>=max(0,k) when
the virtuals are the extreme visited sites; in general the leftmost/rightmost
visited site can be pushed out by deposits beyond [min(0,k),max(0,k)].

We handle this by a transfer DP that emits, for a fixed span [SL,SR], the
GF (polynomial in x) of all feasible deposit-sequences on edges [SL,SR) whose
visited-site set has min exactly SL and max exactly SR.  Summed over all
SL<=min(0,k), SR>=max(0,k).  Because the cost is local + two special sites,
the per-span GF factors into: left-boundary block (site SL), a chain of interior
edges/sites, and right-boundary block (site SR), with the catalytic w-chain.

Implementation: a single left-to-right polynomial DP over edges in
[SL, SR), state = w = |a_{prev edge}|, with x marking accumulated length.  The
boundary sites 0 and k inject the virtual matching cost via boundary_site_cost.
We require the FIRST edge to be "active at its left" (so site SL is genuinely a
visited boundary) and the LAST edge "active at its right" (site SR visited),
to avoid double counting spans.

We truncate x at degree N and cap |a_j| at N (a deposit of magnitude m costs
>= 3m in the bulk, but on travel edges costs less; |a_j|<=N is a safe cap for
coefficients up to x^N since each unit of |a_j| adds >=1 to the length).
"""
import sys, importlib.util, os
from collections import defaultdict
from functools import lru_cache

HERE=os.path.dirname(os.path.abspath(__file__)); ZP=os.path.dirname(HERE)
_S=list(sys.argv)
spec=importlib.util.spec_from_file_location("lf",os.path.join(ZP,"lamp_formula.py"))
lf=importlib.util.module_from_spec(spec); sys.argv=["lf","0"]; spec.loader.exec_module(lf)
sys.argv=_S
site_cost=lf.site_cost

def f_of(j,k):
    return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def edge_updn(f,m): return (m+f)//2,(m-f)//2

# ---- exact virtual-site matching cost (only used at sites 0 and k) ----------
@lru_cache(maxsize=None)
def boundary_site_cost(aL,fL, aR,fR, is0, isk, eps, delta):
    best=None
    for lamL in range(0,3):
        mL=max(abs(aL),abs(fL))+2*lamL
        if (mL-fL)%2 or (mL==0 and fL!=0): mL+=1
        uL,dnL=edge_updn(fL,mL)
        for puL in range(uL+1):
            tL=aL+dnL-uL+2*puL
            if tL%2: continue
            pdL=tL//2
            if pdL<0 or pdL>dnL: continue
            for lamR in range(0,3):
                mR=max(abs(aR),abs(fR))+2*lamR
                if (mR-fR)%2 or (mR==0 and fR!=0): mR+=1
                uR,dnR=edge_updn(fR,mR)
                for puR in range(uR+1):
                    tR=aR+dnR-uR+2*puR
                    if tR%2: continue
                    pdR=tR//2
                    if pdR<0 or pdR>dnR: continue
                    arr=[puL,uL-puL,pdR,dnR-pdR]; dep=[pdL,dnL-pdL,puR,uR-puR]
                    if is0: arr[0]+=1
                    if isk:
                        s=2 if delta==1 else 0
                        dep[s+(0 if eps==1 else 1)]+=1
                    if sum(arr)!=sum(dep): continue
                    c=site_cost(tuple(arr),tuple(dep))
                    if c is not None and (best is None or c<best): best=c
    return best

# Polynomial helpers: dict deg->coeff, truncated at N.
def padd(P,Q,N):
    for d,c in Q.items():
        if d<=N: P[d]=P.get(d,0)+c
def pshift(P,s,N):
    return {d+s:c for d,c in P.items() if d+s<=N}

# Allowed deposit values on an edge with indicator f, magnitude <= cap, matching
# parity f (a==f mod2) and nonzero where required.  Returns list of a values.
def deposits(f,cap,allow_zero):
    out=[]
    if allow_zero and f==0:
        out.append(0)
    par=f&1  # 0 for bulk (even), 1 for travel (odd)
    a=1 if par else 2
    while a<=cap:
        if par or a!=0:
            out.append(a); out.append(-a)
        a+=2
    return out

# ---------------------------------------------------------------------------
# Per-slice relaxed GF.  We enumerate the left boundary site SL and right
# boundary site SR with SL <= min(0,k), SR >= max(0,k).  The span edges are
# [SL, SR).  Edge SL must be active-at-left and edge SR-1 active-at-right so that
# sites SL and SR are the extreme visited sites (no double counting).
#
# DP over edges in [SL, SR), state w=|a_prev|, x marks length.  The two virtual
# sites 0 and k get boundary_site_cost; interior sites get max(|a_{j-1}|,|a_j|);
# each edge pays max(|a_j|,|f_j|) (gap->2).
# ---------------------------------------------------------------------------
def slice_gf(eps,delta,k,N,cap):
    K0=min(0,k); K1=max(0,k)
    total=defaultdict(int)
    # SINGLE-SITE span: only possible when k==0 (both virtuals coincide at 0).
    # Visited set is exactly {0}, no edges, the lone site is the virtual site 0
    # carrying BOTH the arrival (start) and departure (end).
    if k==0:
        bc=boundary_site_cost(0,0,0,0,True,True,eps,delta)
        if bc is not None and bc<=N:
            total[bc]+=1
    # SL ranges from some lower bound up to K0; SR from K1 up to some upper bound.
    # A deposit beyond [K0,K1] extends the span. Each extra bulk edge costs >=2
    # (crossing) plus the connecting site >=1 (its active neighbour has |a|>=1),
    # so an extension of L edges costs >= 2L. Hence SL >= K0 - N//2 etc.  We use a
    # tight per-span lower bound: ntrav travel edges cost >=1 each, nbulk bulk
    # edges cost >=2 each, giving a crossing floor; skip spans whose floor > N.
    ntravK=K1-K0
    SLmin=K0-N-1; SRmax=K1+N+1
    for SL in range(SLmin,K0+1):
        for SR in range(K1,SRmax+1):
            if SR<=SL: continue
            ne=SR-SL
            nbulk=ne-ntravK
            # Safe lower bound on this span's MINIMUM relaxed length:
            #   crossing: ntravK travel edges >=1 each, nbulk bulk edges >=2 each.
            # (sites add only more.)  Skip spans whose floor already exceeds N.
            floor=ntravK + 2*nbulk
            if floor>N: continue
            gf=span_gf(eps,delta,k,SL,SR,N,cap)
            for d,c in gf.items():
                total[d]+=c
    return total

def span_gf(eps,delta,k,SL,SR,N,cap):
    """GF over feasible deposit-seqs on edges [SL,SR) whose visited sites have
    min==SL and max==SR.  Length includes edges [SL,SR), all sites [SL,SR]."""
    edges=list(range(SL,SR))
    if not edges:
        # zero-edge span: only the single virtual site (SL==SR impossible here)
        return {}
    # Precompute f per edge.
    fe={j:f_of(j,k) for j in edges}
    # An edge is "active" if a_j!=0 or f_j!=0.  Site s is visited if s in {0,k}
    # or edge s-1 active or edge s active.  We need min visited == SL and
    # max visited == SR.  Site SL visited <=> SL in {0,k} OR edge SL active.
    # Site SR visited <=> SR in {0,k} OR edge SR-1 active.  Plus NO visited site
    # < SL or > SR (guaranteed since edges only in [SL,SR)).  We also must ensure
    # there is no GAP making an interior site beyond -- not needed: span is solid.
    #
    # The catch: a leading run of inactive edges (a=0,f=0) at the left would make
    # the true leftmost visited site > SL.  So require: the leftmost edge with
    # f!=0 OR forced is within reach; more simply we forbid edge SL from being
    # inactive UNLESS SL in {0,k}.  Symmetric on the right.  Interior inactive
    # edges (gap) are allowed but cost 2 (reachability) AND must be enclosed by
    # active edges on both sides (which they are, within a solid span whose ends
    # are active).
    SLvisited_forced = (SL==0 or SL==k)
    SRvisited_forced = (SR==0 or SR==k)
    # DP state: w=|a_prev edge|.  Start before edge SL with a virtual "no prev".
    # site SL is the left boundary (virtual if SL in{0,k} else interior with aL=0).
    # We'll process site s (left of edge s) then edge s.
    # Represent prev as (w_prev, aprev_signed?) -- site cost only needs |a|, and
    # boundary cost needs signed a AND f.  Interior sites need only |a|.  The two
    # virtual sites need the signed a and f of both neighbors.  Since virtual
    # sites are at fixed positions 0 and k, we special-case them by tracking the
    # signed deposit only when the NEXT site is virtual.  Simplest: track signed
    # (a_prev) always; state count is O(cap).  We compress by |a| for interior.
    #
    # Implementation: states = dict keyed by signed a_prev -> poly(dict deg->cnt).
    # "a_prev = None" sentinel for "no previous edge yet" (before SL).
    NONE=10**9
    states={NONE:{0:1}}
    for idx,j in enumerate(edges):
        fj=fe[j]
        is_first=(idx==0)
        is_last=(idx==len(edges)-1)
        # site j is to the LEFT of edge j.  It's virtual iff j in {0,k}.
        site_is0=(j==0); site_isk=(j==k)
        site_virtual=site_is0 or site_isk
        # allowed deposits on edge j:
        #   first edge: must be active-at-left unless SLvisited_forced.
        #     active-at-left means a_j!=0 or f_j!=0.  If f_j!=0 it's auto active.
        #   last edge: must be active-at-right unless SRvisited_forced.
        # A single edge is both first and last when len==1.
        allow_zero = True
        if is_first and not SLvisited_forced and fj==0:
            allow_zero=False  # need a_j!=0 to make site SL visited
        if is_last and not SRvisited_forced and fj==0:
            allow_zero=False  # need a_j!=0 to make site SR visited
        dep_list=deposits(fj,cap,allow_zero)
        # gap edge cost: if a_j==0 and f_j==0 -> crossing forced to 2; else max(|a|,|f|)
        nstates=defaultdict(lambda:defaultdict(int))
        for ap,poly in states.items():
            for aj in dep_list:
                # crossing cost of edge j
                if aj==0 and fj==0:
                    cross=2
                else:
                    cross=max(abs(aj),abs(fj))
                # site j cost (between edge j-1 [=ap] and edge j [=aj])
                if ap==NONE:
                    aL=0; fL=0
                else:
                    aL=ap; fL=f_of(j-1,k)
                if site_virtual:
                    bc=boundary_site_cost(aL,fL,aj,fj,site_is0,site_isk,eps,delta)
                    if bc is None: continue
                    scost=bc
                else:
                    scost=max(abs(aL),abs(aj))
                add=cross+scost
                tgt=nstates[aj]
                for d,c in poly.items():
                    nd=d+add
                    if nd<=N: tgt[nd]+=c
        states={a:dict(p) for a,p in nstates.items() if p}
        if not states: return {}
    # Close out: site SR is to the RIGHT of last edge (edge SR-1).
    out=defaultdict(int)
    site_is0=(SR==0); site_isk=(SR==k)
    site_virtual=site_is0 or site_isk
    for ap,poly in states.items():
        if ap==NONE: continue
        fL=f_of(SR-1,k)
        if site_virtual:
            bc=boundary_site_cost(ap,fL,0,0,site_is0,site_isk,eps,delta)
            if bc is None: continue
            scost=bc
        else:
            scost=abs(ap)  # max(|a_prev|, 0)
        for d,c in poly.items():
            nd=d+scost
            if nd<=N: out[nd]+=c
    return dict(out)

def relaxed_sequence(N, cap=None, kmax=None, verbose=False):
    if cap is None: cap=N
    if kmax is None: kmax=N+1
    total=defaultdict(int)
    for k in range(-kmax,kmax+1):
        for eps in (1,-1):
            for delta in (0,1):
                gf=slice_gf(eps,delta,k,N,cap)
                for d,c in gf.items():
                    if d<=N: total[d]+=c
        if verbose: print(f"  k={k} done", flush=True)
    return [total[n] for n in range(0,N+1)]

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 18
    seq=relaxed_sequence(N)
    print("v_n =", seq)
    ref=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,
         12959,19949,30640,46905,71699,109490,166969,254047,386192,586349,
         889599,1347444,2039911,3084135]
    L=min(len(seq),len(ref))
    ok=all(seq[n]==ref[n] for n in range(L))
    print(f"MATCHES reference (first {L}):", ok)
    if not ok:
        for n in range(L):
            if seq[n]!=ref[n]:
                print(f"  MISMATCH n={n}: got {seq[n]} ref {ref[n]}")
