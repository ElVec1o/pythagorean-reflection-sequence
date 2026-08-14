# Build the EXACT cycle count as: c = c_interior + corr(site0) + corr(sitek),
# where c_interior = sum over gap blocks NOT touching any marker of block_len, PLUS for
# blocks touching a marker, the part strictly away from the marker. We then TABULATE the
# per-marker boundary correction as a function of local data and confirm it is bounded.
#
# Cleaner: define c_interior = sum over interior gap edges j (lo<j<hi-? ) ... let's just
# define, for each gap edge, whether it is "marker-adjacent" (one of its two sites is a
# marker 0 or k). Non-marker-adjacent gap edges ALWAYS = 1 cycle (verified separately).
# Marker-adjacent gap edges contribute 0 or 1 depending on the junction. We tabulate that.
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def analyze(eps,dl,k,a):
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    trav=list(range(0,k)) if k>0 else (list(range(k,0)) if k<0 else [])
    vsites={0,k}
    for j in nz: vsites|={j,j+1}
    for j in trav: vsites|={j,j+1}
    lo=min(vsites); hi=max(vsites)
    M={0,k}
    isgap=lambda j:(a.get(j,0)==0 and f_of(j,k)==0)
    c_nonmarker=0
    marker_adj_gaps=[]   # gap edges with a marker at one site
    for j in range(lo,hi):
        if isgap(j):
            sites_marker = (j in M) or (j+1 in M)
            if not sites_marker:
                c_nonmarker+=1
            else:
                marker_adj_gaps.append(j)
    return lo,hi,c_nonmarker,marker_adj_gaps

# First: verify NON-marker-adjacent gap edges each = exactly 1 cycle, by checking
# c_true - c_nonmarker = (correction from marker-adjacent gaps only), bounded.
maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
RAD=maxd+8
dist=LL.bfs(RAD)
from collections import Counter
corr_dist=Counter()
nmarkeradj=Counter()
viol=0
for (e,dl,k,L),tl in dist.items():
    rl=relaxed_len(e,dl,k,L)
    if rl is None or rl>tl or rl>maxd: continue
    ct=(tl-rl)//2
    lo,hi,cnm,madj=analyze(e,dl,k,L)
    corr=ct-cnm   # contribution attributed to marker-adjacent gaps
    corr_dist[corr]+=1
    nmarkeradj[len(madj)]+=1
    # the correction must be between 0 and len(madj)
    if corr<0 or corr>len(madj):
        viol+=1
        if viol<=10: print("VIOL",rl,tl,ct,cnm,corr,len(madj),(e,dl,k,dict(L)))
print(f"c_true - c_nonmarker distribution: {dict(sorted(corr_dist.items()))}")
print(f"#marker-adjacent gaps distribution: {dict(sorted(nmarkeradj.items()))}")
print(f"violations (corr outside [0,#madj]): {viol}")
print("=> if violations==0 and corr<=#madj always, the interior (non-marker) gap rule is")
print("   EXACT (1 cycle each) and only a bounded per-marker boundary correction remains.")
