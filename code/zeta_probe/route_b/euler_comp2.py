#!/usr/bin/env python3
"""
Refined open-component count matching the lamp DP EXACTLY.

For a cut c and a fixed Euler trail T:
  #open components on slot c = number of connectivity classes among the m_c
  parallel slot-c edges, where two slot-c edges are joined iff T connects them
  through the LEFT block L_c = {<= c} (i.e. there is a sub-walk of T inside L_c
  whose two ends are these two slot-c edges), UNION the class containing the
  trail-start s if s in L_c, UNION class with e if e in L_c.

Equivalently: contract L_c to a single super-structure following T's wiring;
slot-c edges hanging off it group by which connected piece of (T restricted to
L_c plus the slot-c half-edges) they attach to.

We compute this directly: restrict T to the subgraph induced by edges with
slot < c (fully left) PLUS slot == c edges as pendant half-edges, then take
connected components in the partial pairing defined by T at each site.

Simplest exact method: replay the SITE-sweep pairing exactly as the lamp DP does,
but for a FIXED trail T (so pairing at each site is determined by T's two
incidences). Build union-find over slot-c edges using T's transitions at sites<=c.
"""
import sys
from itertools import permutations
from collections import defaultdict

def build(m, A):
    sites=list(range(A, A+len(m)+1))
    adj={v:[] for v in sites}
    edge_slot=[]; eid=0
    for idx,mj in enumerate(m):
        j=A+idx
        for _ in range(mj):
            adj[j].append((j+1,eid)); adj[j+1].append((j,eid)); edge_slot.append(j); eid+=1
    return sites, adj, edge_slot, eid

def euler_trails(adj,s,e,ne,cap=200000):
    results=[]; used=[False]*ne; path=[]
    def rec(v,cnt):
        if len(results)>=cap: return
        if cnt==ne:
            if v==e: results.append(tuple(path))
            return
        for (w,eid) in adj[v]:
            if not used[eid]:
                used[eid]=True; path.append(eid); rec(w,cnt+1); path.pop(); used[eid]=False
    rec(s,0); return results

def comps_on_cut(T, edge_slot, verts, c, s, e):
    """Union-find over slot-c edge ids, joining two if T transits between them
    through L_c. We traverse T; maintain a 'pending left-open end' = the last
    slot-c edge by which we ENTERED L_c (or the start s if s in L_c). When we
    LEAVE L_c via a slot-c edge, we union the entry edge with the exit edge."""
    parent={}
    def find(x):
        while parent.get(x,x)!=x:
            parent[x]=parent.get(parent[x],parent[x]); x=parent[x]
        return x
    def union(a,b):
        if a is None or b is None: return
        ra,rb=find(a),find(b)
        if ra!=rb: parent[rb]=ra
    slotc_edges=[eid for eid,sl in enumerate(edge_slot) if sl==c]
    for x in slotc_edges: parent[x]=x
    START='S'; parent[START]=START
    # walk the trail; we are at verts[0]=s, edges T[i] go verts[i]->verts[i+1]
    in_left = (verts[0] <= c)
    entry = START if in_left else None   # the slot-c edge (or START) by which we entered L_c
    for i,eid in enumerate(T):
        sl=edge_slot[eid]
        a_v, b_v = verts[i], verts[i+1]
        if sl==c:
            # crossing the cut
            if a_v<=c and b_v>c:
                # leaving L_c via edge eid; union entry with eid
                union(entry, eid)
                in_left=False; entry=None
            elif a_v>c and b_v<=c:
                # entering L_c via edge eid
                in_left=True; entry=eid
            else:
                # slot-c edge but both endpoints same side? impossible for slot c
                pass
        # if e (end) lies in L_c and trail ends there, the final entry stays open
    # if the trail ENDS inside L_c, union entry with END marker (its own class, ok)
    # count classes among slotc_edges, plus whether START joined (start in L_c adds
    # connectivity but is its own anchor). #open comps = #distinct find() over
    # slotc_edges (START merges some but doesn't reduce count of *edge* classes
    # unless it links two edges).
    roots=set(find(x) for x in slotc_edges)
    return len(roots)

def analyze(m, A, s, e, cap=200000):
    sites, adj, edge_slot, ne = build(m,A)
    slots=[A+i for i in range(len(m)) if m[i]>0]
    trails=euler_trails(adj,s,e,ne,cap)
    if not trails: return None
    best=None; detail=None
    for T in trails:
        verts=[s]; cur=s
        for eid in T:
            j=edge_slot[eid]; nxt=j+1 if cur==j else j; verts.append(nxt); cur=nxt
        maxc=0; per={}
        for c in slots:
            cc=comps_on_cut(T,edge_slot,verts,c,s,e)
            per[c]=cc; maxc=max(maxc,cc)
        if best is None or maxc<best:
            best=maxc; detail=(T,verts,per)
    return best, len(trails), detail

if __name__=='__main__':
    tests=[
        ([2,2], 0, 0, 0),
        ([2,4,2], 0, 0, 0),
        ([4,4], 0, 0, 0),
        ([2,2,2], 0, 0, 0),
        ([6,6], 0, 0, 0),
        ([4,6,4], 0, 0, 0),
        ([2,2,2,2], 0, 0, 0),
        ([8], 0, 0, 0),     # 8 parallel edges, trail 0->0: m_0=8
        ([6,2,6], 0, 0, 0),
        ([8,8], 0, 0, 0),
    ]
    for (m,A,s,e) in tests:
        out=analyze(m,A,s,e)
        if out is None:
            print(f"m={m}: NO trail"); continue
        best,nt,detail=out
        T,verts,per=detail
        print(f"m={m} {s}->{e}: MIN-over-trails max-open-comps={best} (#trails={nt})  per-cut={per}")
