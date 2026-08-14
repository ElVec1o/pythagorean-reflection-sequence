# Refined cycle rule: c = sum over maximal blocks of consecutive interior gap edges of
#   (block_length - shielded) where shielded in {0,1,2} = number of block ends adjacent to
#   a marker site (0 or k) that provides free connectivity.
# Test several variants to find the exact rule.
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def gap_blocks(eps,dl,k,a):
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    trav=list(range(0,k)) if k>0 else (list(range(k,0)) if k<0 else [])
    vsites={0,k}
    for j in nz: vsites|={j,j+1}
    for j in trav: vsites|={j,j+1}
    lo=min(vsites); hi=max(vsites)
    isgap=lambda j: (a.get(j,0)==0 and f_of(j,k)==0)
    blocks=[]
    j=lo
    while j<hi:
        if isgap(j):
            s=j
            while j<hi and isgap(j): j+=1
            blocks.append((s,j))  # [s,j) gap edges; sites s..j
        else:
            j+=1
    return blocks, lo, hi

def predict(eps,dl,k,a, mode):
    blocks,lo,hi=gap_blocks(eps,dl,k,a)
    markers={0,k}
    c=0
    for s,e in blocks:
        Lblk=e-s  # number of gap edges
        # block occupies edges s..e-1, sites s..e
        left_site=s; right_site=e
        ends_at_marker = (left_site in markers) + (right_site in markers)
        if mode=='raw':
            c+=Lblk
        elif mode=='minus_marker_ends':
            c+=max(0, Lblk - ends_at_marker)
        elif mode=='minus1_if_any_marker':
            c+=Lblk - (1 if ends_at_marker>=1 else 0)
    return c

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
RAD=maxd+8
dist=LL.bfs(RAD)
modes=['raw','minus_marker_ends','minus1_if_any_marker']
stats={m:0 for m in modes}
n=0
examples={m:[] for m in modes}
for (e,dl,k,L),tl in dist.items():
    rl=relaxed_len(e,dl,k,L)
    if rl is None or rl>tl or rl>maxd: continue
    ctrue=(tl-rl)//2
    n+=1
    for m in modes:
        cp=predict(e,dl,k,L,m)
        if cp!=ctrue:
            stats[m]+=1
            if len(examples[m])<12: examples[m].append((rl,tl,ctrue,cp,e,dl,k,dict(L)))
print(f"tested {n} elements rl<= {maxd}")
for m in modes:
    print(f"  mode {m}: {stats[m]} mismatches")
for r in examples['minus_marker_ends'][:15]:
    print("   [minus_marker_ends] ",r)
