#!/usr/bin/env python3
"""
FAST defect characterization via the closed-form relaxed length (Lemma C/D) and a
direct connectivity check on the geodesic multigraph.

A group element is (eps,delta,k; a) with a = lamp deposit vector.
Relaxed length (Lemma C/D), with optimal crossings m_j = max(|a_j|,|f_j|) and
interior site cost max(|a_{j-1}|,|a_j|), boundary virtual costs at 0,k:
   relaxed_len = sum_{j in span} m_j*  +  sum_{sites in span} sitecost.
We use the boundary_site_cost from catalytic_funceq for the two virtual sites and
the max formula interiorly, exactly as fast_relaxed3 does (validated v_n).

CONNECTIVITY of the geodesic multigraph: with m_j = max(|a_j|,|f_j|) (>=1 on the
active span; gap edges inside span are forced to m=2), the multigraph Gamma on the
span sites has slot j carrying m_j parallel edges.  It is connected on the span iff
NO interior slot has m_j = 0 -- but inside the span gap edges are forced m=2, so
Gamma is ALWAYS connected as a graph on the span vertices.  The real disconnection
comes from EVEN CYCLES that the Euler trail cannot absorb without a crossing, i.e.
the *parity/handshake* obstruction, which the validated TRUE DP detects.

So 'connectivity defect' is NOT mere graph-disconnection of Gamma; it is the
Euler-trail realizability with the single-trail constraint.  To get it exactly and
fast we DON'T recompute the metric; we just ask the validated lamp_profile.solve
(true) vs a relaxed solve.  But that is slow.

Instead, here we EXACTLY enumerate the defect by DIRECTLY enumerating deposit
configs and computing relaxed length, building v_n from configs; then we mark a
config as 'true-feasible at relaxed length' iff its geodesic multigraph admits a
single Euler trail s->e (connectivity of the multigraph on its nonzero-degree
support, with the right degree parity).  u_n = #elements whose MINIMAL relaxed
representative is true-feasible OR whose true length (relaxed+2*ncycles) ...

This still needs the metric.  So: we restrict to the QUESTION that matters --
is the TRAVEL-only sub-ensemble connectivity-defect-free?  We test it directly by
constructing pure-travel + odd-deposit configs and checking single-Euler-trail.
"""
import sys, os, importlib.util
from itertools import product
from collections import defaultdict

HERE=os.path.dirname(os.path.abspath(__file__))
spec=importlib.util.spec_from_file_location("cf",os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf)
bsc=cf.boundary_site_cost

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def multigraph_connected_single_trail(mvec, A, s, e):
    """mvec: multiplicities for slots A..A+len-1. s,e = trail endpoints (sites).
       Returns True iff the multigraph (path with mj parallel edges) admits a
       single Euler trail from s to e:
         - all edges in ONE connected component (on nonzero-degree vertices + s,e),
         - degree parity: exactly the two odd-degree vertices are s,e (or none and s==e)."""
    sites=list(range(A, A+len(mvec)+1))
    deg={v:0 for v in sites}
    nedges=0
    # union-find over sites with >=1 incident edge
    parent={}
    def find(z):
        parent.setdefault(z,z)
        while parent[z]!=z:
            parent[z]=parent[parent[z]]; z=parent[z]
        return z
    def union(p,q):
        rp,rq=find(p),find(q)
        if rp!=rq: parent[rp]=rq
    for idx,m in enumerate(mvec):
        if m==0: continue
        j=A+idx
        deg[j]+=m; deg[j+1]+=m; nedges+=m
        union(j,j+1)
    if nedges==0:
        return s==e
    # connectivity: all positive-degree vertices, plus s and e, in one component
    comp_verts=[v for v in sites if deg[v]>0]
    roots=set(find(v) for v in comp_verts)
    # s,e must be attached to the edge-component (if they have degree 0 they must
    # coincide with a positive-degree vertex's component endpoint)
    if deg.get(s,0)==0 or deg.get(e,0)==0:
        # s or e isolated from edges => no trail unless trivial
        if not (deg.get(s,0)>0 and deg.get(e,0)>0):
            return False
    roots.add(find(s)); roots.add(find(e))
    if len(roots)!=1: return False
    odd=[v for v in sites if deg[v]%2==1]
    if s==e:
        return len(odd)==0
    else:
        return set(odd)=={s,e}

def test_pure_travel_and_odd():
    """Enumerate pure-travel elements: k!=0, deposits a_j ONLY on travel slots [0,k)
       (or (k,0]), all |a_j| ODD (parity-matched to f), magnitudes in {1,3,5}.
       Geodesic m_j = |a_j| (>=1).  Check single Euler trail s=0 -> e=k.
       Hypothesis: ALWAYS realizable (no connectivity defect)."""
    bad=0; tot=0
    for k in list(range(1,7))+list(range(-6,0)):
        slots=list(range(0,k)) if k>0 else list(range(k,0))
        A=min(slots); L=len(slots)
        for combo in product([1,3,5],repeat=L):
            # signed deposits don't change |a|=m; sign affects metric not connectivity
            mvec=[combo[i] for i in range(L)]  # m_j = |a_j| (odd, matches f parity)
            tot+=1
            ok=multigraph_connected_single_trail(mvec,A,0,k)
            if not ok: bad+=1
    print(f"PURE-TRAVEL (odd deposits on [0,k)) single-Euler-trail: {tot-bad}/{tot} realizable, {bad} fail")
    return bad

def test_travel_with_interior_lamps():
    """Travel interval [0,k) but ALSO allow EVEN lamp deposits on travel slots
       (a_j even -> m_j = max(|a_j|,1) = |a_j| if >0 else 1). Plus possibly extra
       even bumps. Check when single trail fails (=> defect candidate)."""
    bad=0; tot=0; fails=[]
    for k in range(1,6):
        slots=list(range(0,k)); A=0; L=k
        # each slot: m_j from {1,2,3,4} (1,3 odd=travel-with-odd-lamp; 2,4 even cycle added)
        for combo in product([1,2,3,4],repeat=L):
            mvec=list(combo); tot+=1
            ok=multigraph_connected_single_trail(mvec,A,0,k)
            if not ok:
                bad+=1
                if len(fails)<8: fails.append((k,tuple(combo)))
    print(f"TRAVEL with even bumps inside: {tot-bad}/{tot} realizable, {bad} fail single-trail")
    for fl in fails: print("   fail:",fl)
    return bad

def test_gap_disconnection():
    """The clearest defect: a GAP. Element with a lamp bump at a site OUTSIDE the
       travel interval, separated by a gap. Geodesic relaxed: gap slot m=0 =>
       multigraph disconnected => isolated cycle => +2 true.
       e.g. k=2 (travel slots 0,1), plus a bump at slot 4 (a_4=2) with gap slots 2,3
       having a=0 => relaxed m=0 there (they are OUTSIDE the active span? in fast_relaxed
       gaps INSIDE span are forced m=2). The bump is OUTSIDE [0,k]: it extends span.
       Span = [0, 5]; interior gap slots 2,3 forced m=2 -> CONNECTED again!
       So in THIS metric there is no free gap; the connection is forced and PAID.
       => the defect is NOT graph-gaps. It must be the EVEN-CYCLE parity obstruction."""
    # Demonstrate: bump outside, span fills gaps with m=2 -> connected, paid.
    # m for span [0,5]: slots 0,1 (travel,m=1), 2,3 (gap forced m=2), 4 (bump a=2,m=2)
    mvec=[1,1,2,2,2]; A=0
    ok=multigraph_connected_single_trail(mvec,A,0,2)
    print(f"bump-outside (gaps forced m=2) [m={mvec}] single-trail 0->2: {ok}")
    # vs if gaps were FREE (m=0) the bump at slot4 would be an isolated cycle:
    mvec2=[1,1,0,0,2]
    ok2=multigraph_connected_single_trail(mvec2,A,0,2)
    print(f"bump-outside (gaps FREE m=0) [m={mvec2}] single-trail 0->2: {ok2}  (relaxed allows, true forbids)")

if __name__=="__main__":
    print("="*70)
    b1=test_pure_travel_and_odd()
    print("-"*70)
    b2=test_travel_with_interior_lamps()
    print("-"*70)
    test_gap_disconnection()
