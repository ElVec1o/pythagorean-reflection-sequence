# Test: is the connectivity defect c(g) determined purely by the BULK runs (the
# non-travel deposits), independent of the travel length |k|?
# We take cycle-bearing elements and see if c depends on k beyond the bulk pattern.
#
# More precisely: define the bulk pattern relative to the two marker sites 0 and k.
# Travel edges occupy [min(0,k), max(0,k)). Bulk deposits are at edges OUTSIDE [0,k)
# (strictly, the lamp deposits with even a; travel edges carry odd a tied to f).
# Claim to test: cycles are created only by even (bulk) deposits separated from the
# spine {0..k} by a reachability gap; c counts the # of such detached components.
import sys, os
from collections import defaultdict, Counter
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

# combinatorial predictor of c: build the multigraph with optimal m_j=max(|a_j|,|f_j|)
# (gap edges inside span forced to 2), find connected components of POSITIVE-multiplicity
# edges, count those NOT containing a marker site (0 or k). Each is a forced cycle (c+=).
def predict_c(eps,dl,k,a):
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    trav=list(range(0,k)) if k>0 else (list(range(k,0)) if k<0 else [])
    vsites={0,k}
    for j in nz: vsites|={j,j+1}
    for j in trav: vsites|={j,j+1}
    lo=min(vsites); hi=max(vsites)
    edges=list(range(lo,hi))
    mult={}
    for j in edges:
        aj=a.get(j,0); fj=f_of(j,k); mj=max(abs(aj),abs(fj))
        if mj==0: mj=2   # reachability gap edge forced
        mult[j]=mj
    # connected components of sites lo..hi via edges with mult>0 (all are >0 here by force)
    # On a line, comps are maximal runs of consecutive edges with mult>0. But ALL span edges
    # are forced >0, so the whole span is ONE component => predict_c would be 0. That's wrong.
    # The cycle is subtler: it's about the EULERIAN realizability with the matching, not raw
    # connectivity of forced edges. So this naive predictor fails; cycles come from the
    # PAIRING (a strand returning on the same edge forms a detached 2-cycle if it can't link
    # to the spine). We instead just REPORT the structure for inspection.
    return None

# Instead: tabulate, for each cycle element, the "bulk signature": deposits at edges
# outside [min(0,k),max(0,k)) and their distance from the spine.
maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
RAD=maxd+8
dist=LL.bfs(RAD)
rows=[]
for (e,dl,k,L),tl in dist.items():
    rl=relaxed_len(e,dl,k,L)
    if rl is None or rl>tl or rl>maxd: continue
    c=(tl-rl)//2
    if c==0: continue
    a=dict(L)
    K0,K1=min(0,k),max(0,k)
    # bulk deposits = even-a edges outside [K0,K1)
    bulk=[(j,a[j]) for j in sorted(a) if not (K0<=j<K1)]
    rows.append((rl,c,k,tuple(bulk)))
# Does c correlate with # of bulk deposits separated by gaps from the spine?
# Group by (sorted bulk pattern shifted to be spine-relative) and see if c is constant.
print(f"cycle rows (rl<= {maxd}): {len(rows)}")
# For each, compute number of "detached even deposits": even deposits at edge j such that
# there's a gap (no forced positive edge) between j and the spine [K0,K1].
# But forced gap edges are filled with m=2... The real criterion (from lamp_profile) is
# whether the deposit's up/down strands can be matched into the spine. Empirically c counts
# the number of even deposits lying STRICTLY beyond an adjacent spine edge.
def detached_count(k,bulk):
    K0,K1=min(0,k),max(0,k)
    cnt=0
    for j,aj in bulk:
        # distance from spine interval [K0,K1] in edges
        if j>=K1: d=j-K1+1   # edges between spine-right-site K1 and this edge's left site j
        elif j<K0: d=K0-(j+1)+1
        else: d=0
        # a single isolated even deposit at gap distance>=1 forms 1 cycle per "step out"?
        cnt += max(0,d)  # heuristic
    return cnt
hits=0
for rl,c,k,bulk in rows:
    pc=detached_count(k,bulk)
    if pc==c: hits+=1
print(f"detached_count heuristic matches c: {hits}/{len(rows)}")
# show mismatches structure
mm=[(rl,c,k,bulk,detached_count(k,bulk)) for rl,c,k,bulk in rows if detached_count(k,bulk)!=c]
for r in mm[:20]: print("  MM",r)
