# Extract the exact shielding correction. Hypothesis: c(g) = G - S where
#   G = total # gap edges in span,
#   S = shield(start@0) + shield(end@k),  each shield in {0,1,2}.
# The start marker arrives at site 0 from the LEFT (below), so it can absorb gap edges
# extending to the LEFT of site 0 (a left-running block of gaps adjacent to site 0): shield
# = length of the maximal gap block immediately on the marker's connecting side, capped.
# We MEASURE shield empirically for isolated single-marker configs (k=0 has both markers
# coincident, messy; use k!=0 with bulk on ONE side only to isolate one marker).
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)
def gapcount(eps,dl,k,a):
    a=dict(a); nz=[j for j in a if a[j]!=0]
    trav=list(range(0,k)) if k>0 else (list(range(k,0)) if k<0 else [])
    vsites={0,k}
    for j in nz: vsites|={j,j+1}
    for j in trav: vsites|={j,j+1}
    lo=min(vsites); hi=max(vsites); G=0
    for j in range(lo,hi):
        if a.get(j,0)==0 and f_of(j,k)==0: G+=1
    return G,lo,hi

def c_of(eps,dl,k,a):
    rl=relaxed_len(eps,dl,k,a); tl=LL.solve(eps,dl,k,dict(a))
    if rl is None or tl is None: return None
    return (tl-rl)//2

# Isolate START marker: put bulk run to the LEFT of site 0, travel to the right (k>0 with
# a=+1 on travel edges), and a single even deposit at edge -(g+1) (g gap edges -1..-(g) to
# the left of site 0). Measure c; G = g. shield_start = G - c.
print("START marker shielding (left bulk, travel right). eps,dl vary; single left deposit, g left-gaps")
for eps in (1,-1):
  for dl in (0,1):
    row=[]
    for g in range(0,5):
        edge=-(g+1)
        a={edge:2}
        for j in range(0,2): a[j]=1   # short travel k=2 to the right
        k=2
        c=c_of(eps,dl,k,a)
        G,lo,hi=gapcount(eps,dl,k,a)
        # gaps to the LEFT of 0 are edges -1..edge+1
        row.append((g,G,c,(G-c) if c is not None else None))
    print(f" eps={eps} dl={dl}: (g, G, c, shield=G-c) -> {row}")

print("\nEND marker shielding (bulk run to the RIGHT of site k, travel from 0..k).")
for eps in (1,-1):
  for dl in (0,1):
    row=[]
    for g in range(0,5):
        k=2
        edge=k+g  # deposit g gaps past site k
        a={edge:2}
        for j in range(0,k): a[j]=1
        c=c_of(eps,dl,k,a)
        G,lo,hi=gapcount(eps,dl,k,a)
        row.append((g,G,c,(G-c) if c is not None else None))
    print(f" eps={eps} dl={dl}: (g, G, c, shield=G-c) -> {row}")
