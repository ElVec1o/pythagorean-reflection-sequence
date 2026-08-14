#!/usr/bin/env python3
"""
ROUTE A -- FAST relaxed sequence v_n for A396406 (single-sweep transfer DP).

Same validated closed form as fast_relaxed.py (Lemma D, checked exhaustively),
but ONE left-to-right sweep per slice instead of an O(N^2) (SL,SR) double loop.

Per slice (eps,delta,k): sweep edges j over the window [K0-W, K1+W) where
K0=min(0,k), K1=max(0,k), W=N+1.  State during the sweep:
    phase 0  -- span not yet started (only inactive bulk edges so far);
    phase 1  -- inside the active span, carrying a_prev (signed) and length;
    phase 2  -- span ended (only inactive bulk edges allowed after).
The active span [SL,SR) is delimited by the first and last active edges; SL/SR
are the extreme visited sites.  Constraint: site SL visited requires edge SL
active-at-left OR SL in {0,k}; symmetric at SR.  Since virtuals {0,k} are ALWAYS
visited, the span MUST cover [K0,K1]; we enforce that the sweep is in phase 1
across all of [K0,K1].

Cost accounting (length marked by x, truncated at degree N):
  edge j: cross = max(|a_j|,|f_j|), forced to 2 if a_j==0 and f_j==0 (gap edge
          inside the active span).
  site j (left of edge j): interior -> max(|a_{j-1}|,|a_j|); virtual (j in {0,k})
          -> boundary_site_cost.  The closing site SR handled at span end.

State key for the catalytic transfer: (phase, a_prev) where a_prev is the signed
deposit of the previous edge (needed signed only when the NEXT site is virtual;
elsewhere only |a_prev| matters, but carrying signed costs at most 2x states).
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

@lru_cache(maxsize=None)
def deposits(f,cap):
    """All deposit values a with a==f (mod2), |a|<=cap, nonzero if f!=0."""
    out=[]
    par=f&1
    a=1 if par else 2
    while a<=cap:
        out.append(a); out.append(-a); a+=2
    return tuple(out)

# poly = dict deg->count, truncated at N.
def slice_gf(eps,delta,k,N,cap):
    K0=min(0,k); K1=max(0,k)
    JLO=K0-(N+1); JHI=K1+(N+1)   # edges [JLO, JHI)
    # state: (phase, a_prev) -> poly(dict deg->cnt).  a_prev signed; in phase 0/2
    # a_prev is irrelevant (use sentinel None).
    NONE=None
    # phase 0 = before span; phase 1 = in span; phase 2 = after span.
    states={(0,NONE):{0:1}}
    out_total=defaultdict(int)

    # single-site span (k==0): only site 0, both virtual events, no edges.
    if k==0:
        bc=boundary_site_cost(0,0,0,0,True,True,eps,delta)
        if bc is not None and bc<=N: out_total[bc]+=1

    for j in range(JLO,JHI):
        fj=f_of(j,k)
        site_is0=(j==0); site_isk=(j==k)
        site_virtual=site_is0 or site_isk
        # the site to the RIGHT of this edge is site j+1; we handle closing
        # (phase1->phase2) when we DECIDE to end the span at edge j (then site
        # j+1 = SR is the closing boundary).  We emit final results when the
        # span has ended AND we've passed K1 (all of [K0,K1] covered).
        ns=defaultdict(lambda:defaultdict(int))
        for (phase,ap),poly in states.items():
            if phase==0:
                # Option A: stay before span -- only if this edge is inactive
                # (a=0,f=0) and we haven't reached a point that forces start.
                # We may NOT skip an edge with f!=0 (travel edge must be active &
                # inside span).  Also cannot skip past K0 without starting (site
                # K0<= must be inside or at span left).  Concretely: if j>=K0 the
                # span must already include site K0<=? -- we require phase becomes
                # 1 no later than edge K0 (so site K0 is covered) ... handled by
                # forbidding phase-0 carry for j>=K0.
                if fj==0 and j<K0:
                    nd=ns[(0,NONE)]
                    for d,c in poly.items(): nd[d]+=c
                # Option B: start the span at this edge (edge j is first active).
                # site j (left boundary SL=j) is virtual iff j in{0,k}, else
                # interior with aL=0 (no previous active edge => site cost
                # max(0,|a_j|)=|a_j|).  But for a NON-virtual SL the site is the
                # span's left end with no left neighbour: cost = |a_j|.
                # The first edge must be ACTIVE (a!=0 or f!=0).  If f!=0 it's auto.
                for aj in _edge_deposits(fj,cap,require_active=True):
                    cross=_cross(aj,fj)
                    if site_virtual:
                        sc=boundary_site_cost(0,0,aj,fj,site_is0,site_isk,eps,delta)
                        if sc is None: continue
                    else:
                        sc=abs(aj)  # max(0,|aj|)
                    add=cross+sc
                    tgt=ns[(1,aj)]
                    for d,c in poly.items():
                        nd=d+add
                        if nd<=N: tgt[nd]+=c
            elif phase==1:
                fL=f_of(j-1,k)
                for aj in _edge_deposits(fj,cap,require_active=False):
                    cross=_cross(aj,fj)
                    if site_virtual:
                        sc=boundary_site_cost(ap,fL,aj,fj,site_is0,site_isk,eps,delta)
                        if sc is None: continue
                    else:
                        sc=max(abs(ap),abs(aj))
                    add=cross+sc
                    tgt=ns[(1,aj)]
                    for d,c in poly.items():
                        nd=d+add
                        if nd<=N: tgt[nd]+=c
            # phase 2 handled at span-close below (we don't iterate trailing edges;
            # trailing inactive bulk edges contribute nothing and don't extend the
            # visited set, so we simply close the span and finalize).

        # Span-CLOSE: any phase-1 state may end its span AFTER edge j, provided
        # the right boundary site SR=j+1 is >= K1 (so [K0,K1] fully covered) AND
        # the last edge j is active-at-right.  Closing pays the SR site cost.
        for (phase,ap),poly in list(states.items()):
            if phase!=1: continue
            # last edge must be active (a_prev!=0 or f_{j}!=0). a_prev is THIS
            # edge's deposit only after we've added it; but here `states` is the
            # PRE-edge-j state, ap = edge (j-1) deposit.  We close spans in the
            # NEXT-state loop instead.  (See finalize after the sweep.)
            pass
        states={kk:dict(vv) for kk,vv in ns.items() if vv}
        # finalize: for any phase-1 state whose CURRENT last edge is edge j and
        # j>=K1-1 (so site j+1=SR>=K1) and edge j active-at-right, close it.
        SR=j+1
        if SR>=K1:
            for (phase,ap),poly in states.items():
                if phase!=1: continue
                # ap = deposit of edge j (the last edge). active-at-right needs
                # ap!=0 OR f_j!=0.  f_j!=0 only if j in[K0,K1); for j>=K1, f_j=0,
                # so require ap!=0 unless SR in {0,k}.
                fLast=fj  # f of edge j
                active_right = (ap!=0) or (fLast!=0)
                site_is0R=(SR==0); site_iskR=(SR==k)
                site_virtualR=site_is0R or site_iskR
                if not active_right and not site_virtualR:
                    continue
                if site_virtualR:
                    sc=boundary_site_cost(ap,fLast,0,0,site_is0R,site_iskR,eps,delta)
                    if sc is None: continue
                else:
                    sc=abs(ap)
                for d,c in poly.items():
                    nd=d+sc
                    if nd<=N: out_total[nd]+=c
        if not states: break
    return out_total

def _cross(aj,fj):
    if aj==0 and fj==0: return 2
    return max(abs(aj),abs(fj))

@lru_cache(maxsize=None)
def _edge_deposits(fj,cap,require_active):
    base=list(deposits(fj,cap))
    if fj==0 and not require_active:
        base=[0]+base   # gap edge allowed (a=0)
    return tuple(base)

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
        if verbose: print(f"  k={k} done",flush=True)
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
                print(f"  MISMATCH n={n}: got {seq[n]} ref {ref[n]}");
