#!/usr/bin/env python3
"""
ROUTE A -- FAST relaxed sequence v_n (single-sweep transfer, correct for all k).

Validated closed form (Lemma D): feasibility a_j==f_j (mod2) on every span edge;
length = sum_j max(|a_j|,|f_j|) [gap->2] + sum_sites (interior max(|a_{j-1}|,|a_j|)
or virtual boundary cost at 0 and k).

SINGLE SWEEP per slice (eps,delta,k).  The active span is [SL, SR) in edges,
[SL, SR] in sites, with SL = leftmost visited site, SR = rightmost.  Since the
virtual sites {0,k} are ALWAYS visited, SL <= K0=min(0,k) and SR >= K1=max(0,k).
The span is a CONTIGUOUS run of edges; outside it edges are inactive (a=0,f=0)
and contribute nothing to length or visited set.

We sweep j from JLO=K0-M to JHI=K1+M.  DP state:
   'pre'           : span has not started (all edges so far inactive);
   ('in', aprev)   : inside the span, last edge had signed deposit aprev;
   'post'          : span ended (no more active edges allowed).
Transitions add edge crossing + the LEFT-site cost of that edge.  When we leave
'in' we also pay the closing right-boundary site cost (SR).

Span legality:
   * first active edge SL: its LEFT site is the left boundary.  If SL in {0,k}
     it's virtual; else interior with no left neighbour -> cost |a_SL|.
   * the whole of [K0, K1] must be inside the span (sites 0,k visited): we enforce
     by requiring state=='in' for every edge j in [K0, K1) and that we have
     started by edge K0 and not ended before K1.
   * last active edge SR-1: its RIGHT site SR is the right boundary.

To keep it a clean linear sweep we DON'T track 'post' explicitly; instead, at
each edge j with j>=K1, an 'in' state may CLOSE (emit result with right boundary
at SR=j+1) provided edge j is active-at-right.  Edges strictly after closing are
inactive and ignored.  Closings at different j are disjoint (different SR), no
double count.  Symmetrically the span may START at any SL<=K0.
"""
import sys, importlib.util, os
from collections import defaultdict
from functools import lru_cache

# Closed-form min-cost matching at a site (replaces the slow recursive site_cost
# in lamp_formula).  Classes 0=L+,1=L-,2=R+,3=R-; cost: same class 0, same-side
# opposite-sign 2, opposite-side 1.  Derived and verified exactly (0/53559).
def site_cost(arr, dep):
    if arr[0]+arr[1]+arr[2]+arr[3] != dep[0]+dep[1]+dep[2]+dep[3]:
        return None
    a0=arr[0]-min(arr[0],dep[0]); d0=dep[0]-min(arr[0],dep[0])
    a1=arr[1]-min(arr[1],dep[1]); d1=dep[1]-min(arr[1],dep[1])
    a2=arr[2]-min(arr[2],dep[2]); d2=dep[2]-min(arr[2],dep[2])
    a3=arr[3]-min(arr[3],dep[3]); d3=dep[3]-min(arr[3],dep[3])
    AL=a0+a1; AR=a2+a3; DL=d0+d1
    x=min(AL, AR-DL+AL)
    lo=AL-DL
    if x<lo: x=lo
    if x<0: x=0
    y=DL-AL+x
    return 2*AL+2*AR-x-y

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)
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
    out=[]; par=f&1; a=1 if par else 2
    while a<=cap: out.append(a); out.append(-a); a+=2
    return tuple(out)

def _cross(aj,fj):
    return 2 if (aj==0 and fj==0) else max(abs(aj),abs(fj))

def slice_gf(eps,delta,k,N,cap):
    K0=min(0,k); K1=max(0,k)
    M=N+1
    JLO=K0-M; JHI=K1+M
    out=defaultdict(int)

    # single-site span: k==0, no edges, lone virtual site 0 carries start+end.
    if k==0:
        bc=boundary_site_cost(0,0,0,0,True,True,eps,delta)
        if bc is not None and bc<=N: out[bc]+=1

    # state dict: key -> poly(dict deg->cnt).  keys: 'pre'  or  ('in',aprev).
    states={'pre':{0:1}}
    for j in range(JLO,JHI):
        fj=f_of(j,k)
        site_is0=(j==0); site_isk=(j==k)
        site_virtual=site_is0 or site_isk
        fL=f_of(j-1,k)
        ns=defaultdict(lambda:defaultdict(int))
        for key,poly in states.items():
            if key=='pre':
                # (a) stay pre: only if edge j inactive AND j < K0 (cannot leave
                #     site K0 unvisited: span must include K0).  Equivalently we
                #     must START no later than edge K0... but the start edge could
                #     be exactly K0.  Inactive carry allowed only while j<K0.
                if fj==0 and j<K0:
                    tgt=ns['pre']
                    for d,c in poly.items(): tgt[d]+=c
                # (b) start span at edge j (j is the first active edge, SL=j).
                #     Require SL<=K0 (so [K0,K1] can be covered): j<=K0.
                if j<=K0:
                    for aj in deposits(fj,cap):   # active: aj!=0 always here (deposits nonzero)
                        cross=_cross(aj,fj)
                        if site_virtual:
                            sc=boundary_site_cost(0,0,aj,fj,site_is0,site_isk,eps,delta)
                            if sc is None: continue
                        else:
                            sc=abs(aj)   # max(0,|aj|), no left neighbour
                        add=cross+sc
                        tgt=ns[('in',aj)]
                        for d,c in poly.items():
                            nd=d+add
                            if nd<=N: tgt[nd]+=c
                    # start with an INACTIVE edge is impossible (first edge must be
                    # active to make site SL visited) UNLESS SL in {0,k}: then the
                    # virtual site is visited regardless, so edge j may be a=0,f=0.
                    if site_virtual and fj==0 and j<=K0:
                        aj=0
                        cross=_cross(aj,fj)
                        sc=boundary_site_cost(0,0,aj,fj,site_is0,site_isk,eps,delta)
                        if sc is not None:
                            add=cross+sc
                            tgt=ns[('in',aj)]
                            for d,c in poly.items():
                                nd=d+add
                                if nd<=N: tgt[nd]+=c
            else:
                aprev=key[1]
                # continue span: edge j may be active or a gap (a=0,f=0) inside span.
                # but if j is a travel edge (f!=0) it MUST be active with matching
                # parity -> deposits(fj) excludes 0 and has right parity.
                cand=list(deposits(fj,cap))
                if fj==0:
                    cand=[0]+cand   # gap edge allowed inside span
                for aj in cand:
                    cross=_cross(aj,fj)
                    if site_virtual:
                        sc=boundary_site_cost(aprev,fL,aj,fj,site_is0,site_isk,eps,delta)
                        if sc is None: continue
                    else:
                        sc=max(abs(aprev),abs(aj))
                    add=cross+sc
                    tgt=ns[('in',aj)]
                    for d,c in poly.items():
                        nd=d+add
                        if nd<=N: tgt[nd]+=c
        states={kk:dict(vv) for kk,vv in ns.items() if vv}
        # CLOSE: an 'in' state whose last edge is j can close with SR=j+1, if
        # SR>=K1 (covers [K0,K1]) and edge j is active-at-right.
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
                for d,c in poly.items():
                    nd=d+sc
                    if nd<=N: out[nd]+=c
        if not states: break
    return out

def relaxed_sequence(N, cap=None, kmax=None, verbose=False):
    if cap is None: cap=N//3+2
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
         889599,1347444,2039911,3084135,4661368,7035665,10617513,16002526,
         24117471,36303371,54649900,82171011]
    L=min(len(seq),len(ref))
    ok=all(seq[n]==ref[n] for n in range(L))
    print(f"MATCHES reference (first {L}):", ok)
    if not ok:
        for n in range(L):
            if seq[n]!=ref[n]:
                print(f"  MISMATCH n={n}: got {seq[n]} ref {ref[n]}")
