# Find the EXACT cycle-count rule by comparing my gap-edge heuristic to the true c per element.
# For each element, compute: relaxed_len, true_len (=> c_true), and my predicted gap-cycle count.
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def my_gap_cycles(eps,dl,k,a):
    # replicate the sweep's gap-edge counting: interior gap edges (a=0,f=0), NOT at virtual
    # sites 0 or k. Count them in the active span [lo,hi).
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    trav=list(range(0,k)) if k>0 else (list(range(k,0)) if k<0 else [])
    vsites={0,k}
    for j in nz: vsites|={j,j+1}
    for j in trav: vsites|={j,j+1}
    lo=min(vsites); hi=max(vsites)
    cnt=0
    for j in range(lo,hi):
        aj=a.get(j,0); fj=f_of(j,k)
        if aj==0 and fj==0:
            cnt+=1   # interior gap edge
    return cnt

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
RAD=maxd+8
dist=LL.bfs(RAD)
mismatch=[]
n=0
for (e,dl,k,L),tl in dist.items():
    rl=relaxed_len(e,dl,k,L)
    if rl is None or rl>tl or rl>maxd: continue
    ctrue=(tl-rl)//2
    cpred=my_gap_cycles(e,dl,k,L)
    n+=1
    if ctrue!=cpred:
        mismatch.append((rl,tl,ctrue,cpred,e,dl,k,dict(L)))
print(f"tested {n} elements (rl<= {maxd}); cycle-rule mismatches: {len(mismatch)}")
for r in mismatch[:40]:
    rl,tl,ct,cp,e,dl,k,L=r
    print(f"  rl={rl} tl={tl} c_true={ct} c_pred={cp} | eps={e} dl={dl} k={k} a={L}")
