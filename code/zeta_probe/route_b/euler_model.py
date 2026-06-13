#!/usr/bin/env python3
"""
Abstract Euler-trail-on-an-interval model, to pin down the open-component count
and test the surgery / interval-graph bound INDEPENDENTLY of the lamp DP.

A geodesic crossing-vector (m_j) gives a multigraph G on the path of sites
A..B+1 with m_j parallel edges in slot j.  A realisation is an Euler trail T
from s=0 to e=k* using each edge once.

We sweep the trail edge-by-edge in TRAIL ORDER and, for each edge-slot j, ask:
how many components of the PARTIAL trail (the prefix processed so far) have a
strand on slot j?  That is the DP's "open components on edge j".

But the DP processes by SITE (left to right), pairing arrivals/departures.
The right notion for the catalytic-variable argument is:

  As we sweep a CUT c left-to-right, the partial pairing assembled from all
  sites <= c induces a set of "dangling" strand-ends on slot c.  Two strand-ends
  on slot c are in the same component iff the partial structure to the left
  connects them.  #components on slot c = number of connectivity classes of the
  m_c parallel edges, as forced by the left structure.

KEY STRUCTURAL FACT to test:  the partial Euler trail, restricted to the left
block L_c = {A..c}, is a disjoint union of trails (the "arcs" the full trail
makes inside L_c).  Each arc either (a) starts and ends on the cut (both
endpoints among the m_c crossing-edges), (b) has one endpoint on the cut and one
at s or e, or (c) is entirely a closed sub-loop.  The number of arcs touching
the cut bounds the open-component count.

We enumerate small G, all Euler trails, and measure the MINIMUM over trails of
the maximum open-component count over cuts.  This is the geodesic-realisable
component bound, computed from first principles (no lamp DP).
"""
import sys
from itertools import permutations
from collections import defaultdict

def euler_trails(adj, s, e, total_edges):
    """adj: dict v -> list of (neighbor, edge_id). Yield Euler trails s->e as
    edge-id sequences. Backtracking; dedupe by edge sequence."""
    # build edge incidence
    results=[]
    used=[False]*total_edges
    path=[]
    # adjacency as list per vertex
    def rec(v, cnt):
        if cnt==total_edges:
            if v==e:
                results.append(tuple(path))
            return
        for (w,eid) in adj[v]:
            if not used[eid]:
                used[eid]=True; path.append(eid)
                rec(w, cnt+1)
                path.pop(); used[eid]=False
    rec(s,0)
    return results

def build_path_multigraph(m, A):
    """m: list of multiplicities for slots A..A+len(m)-1 (slot j between site j and j+1).
    Returns adj over sites A..A+len(m), edge list (slot per edge)."""
    sites=list(range(A, A+len(m)+1))
    adj={v:[] for v in sites}
    edge_slot=[]
    eid=0
    for idx,mj in enumerate(m):
        j=A+idx
        for _ in range(mj):
            adj[j].append((j+1,eid)); adj[j+1].append((j,eid))
            edge_slot.append(j)
            eid+=1
    return sites, adj, edge_slot, eid

def open_components_over_cuts(trail, edge_slot, slots):
    """Given an Euler trail (sequence of edge ids), compute for each cut c the
    number of open components: process trail edges in ORDER, maintain union-find
    over edges; but 'open on slot c' means: among edges of slot c, group them by
    the component (in the partial structure) -- but the partial structure is the
    WHOLE trail here. We instead emulate the SITE-sweep DP differently:

    Simpler faithful measure: sweep cuts c left to right. The partial trail
    'to the left of c' = the set of maximal sub-walks of T contained in L_c.
    Each maximal sub-walk that touches the cut contributes open ends.
    #open components on slot c = number of distinct sub-walks of T|_{L_c} that
    have >=1 edge in slot c OR connect two slot-c edges.

    Cleanest equivalent: contract everything in L_c; the slot-c edges become
    'half-edges' hanging off the contracted-left structure. Two slot-c edges are
    in the same open component iff T connects them THROUGH the left block."""
    res={}
    for c in slots:
        # left block vertices: <= c.  Edges fully in left block: slot < c.
        # slot-c edges cross the cut. Build a graph on slot-c edges where two are
        # connected if T routes from one to the other staying in the left block.
        # We do this via the trail: walk T; track when we are 'in the left block'
        # contiguously and which slot-c edges bound those excursions.
        # Each time T crosses the cut (uses a slot-c edge), it enters/leaves L_c.
        # The excursions of T into L_c are delimited by slot-c crossings (and the
        # trail ends s,e if they lie in L_c).
        # An excursion into L_c that begins with crossing edge x and ends with
        # crossing edge y links x,y into the same open component.
        # Excursions bounded by s or e (trail endpoints in L_c) are 'open ended'.
        cross_positions=[i for i,eid in enumerate(trail) if edge_slot[eid]==c]
        # partition the trail by these crossings into segments; segment between
        # consecutive crossings lies entirely on one side.
        # Determine side of each segment by where the trail currently is.
        # Reconstruct vertex sequence:
        # We need start vertex s. We'll pass it in via closure; recompute below.
        res[c]=cross_positions  # placeholder; real calc in caller
    return res

def analyze(m, A, s, e):
    sites, adj, edge_slot, ne = build_path_multigraph(m, A)
    slots=[A+i for i in range(len(m)) if m[i]>0]
    trails = euler_trails(adj, s, e, ne)
    if not trails:
        return None
    best_over_trails=None
    detail_best=None
    for T in trails:
        # reconstruct vertex sequence
        verts=[s]
        cur=s
        for eid in T:
            j=edge_slot[eid]
            nxt = j+1 if cur==j else j
            verts.append(nxt); cur=nxt
        # for each cut c, count open components via left-block excursions
        maxc=0
        per_cut={}
        for c in slots:
            # excursions of the vertex-walk into L_c={<=c}: maximal runs where
            # vertices <= c.  Each run is a connected piece of T inside L_c.
            # The number of runs that contain at least one slot-c edge endpoint OR
            # contain s/e contributes to open components: actually #open comps on
            # slot c = number of runs of T|_{L_c} that touch the cut (i.e. include
            # a vertex = c with a slot-c edge incident in the trail) -- but every
            # run inside L_c except possibly the s/e-anchored ones is bounded by
            # slot-c crossings.  #runs inside L_c that are NOT closed = open comps.
            # Count maximal runs of consecutive verts all <= c.
            runs=0
            inrun=False
            for v in verts:
                if v<=c:
                    if not inrun: runs+=1; inrun=True
                else:
                    inrun=False
            per_cut[c]=runs
            maxc=max(maxc,runs)
        if best_over_trails is None or maxc<best_over_trails:
            best_over_trails=maxc; detail_best=(T,verts,per_cut)
    return best_over_trails, len(trails), detail_best

if __name__=='__main__':
    # sanity: a few small multigraphs
    tests=[
        ([2], 0, 0, 1),     # 2 parallel edges 0-1, trail 0->0
        ([2,2], 0, 0, 0),
        ([4], 0, 0, 1),
        ([2,4,2], 0, 0, 0),
        ([4,4], 0, 0, 0),
        ([6], 0, 0, 1),
        ([2,2,2], 0, 0, 0),
        ([4,2,4], -1, 0, 0),
    ]
    for (m,A,s,e) in tests:
        out=analyze(m,A,s,e)
        if out is None:
            print(f"m={m} A={A} s={s} e={e}: NO euler trail")
            continue
        best,nt,detail=out
        print(f"m={m} A={A} s={s}->e={e}: min-over-trails max-open-comps = {best}  (#trails={nt})")
        if detail:
            T,verts,per_cut=detail
            print(f"    best trail verts={verts}  per-cut comps={per_cut}")
