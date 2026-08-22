import sys, resource
sys.setrecursionlimit(10000)
try:
    resource.setrlimit(resource.RLIMIT_AS, (3000*1024*1024, resource.RLIM_INFINITY))
except Exception as ex:
    print("rlimit not set:", ex)
# lamp_lib.py lives in code/zeta_probe/route_b/, which is NOT tracked (.gitignore:77).
# Point LAMPLIB at a checkout of it, or set it alongside this file.
import os
sys.path.insert(0, os.environ.get("LAMPLIB", os.path.dirname(os.path.abspath(__file__))))
import lamp_lib as LL

DEPTH = int(sys.argv[1]) if len(sys.argv)>1 else 14
dist = LL.bfs(DEPTH)
print(f"elements enumerated to depth {DEPTH}: {len(dist)}")

def fvec(k, j):
    if k>0:  return 1 if 0<=j<k else 0
    if k<0:  return -1 if k<=j<0 else 0
    return 0

def gap_edges(k, a):
    A = dict(a)
    vis = {0, k}
    for j,v in A.items():
        if v!=0: vis.add(j); vis.add(j+1)
    if k>0:
        for j in range(0,k): vis.add(j); vis.add(j+1)
    elif k<0:
        for j in range(k,0): vis.add(j); vis.add(j+1)
    lo, hi = min(vis), max(vis)
    return [j for j in range(lo,hi) if A.get(j,0)==0 and fvec(k,j)==0]

nogap_tot=nogap_bad=0
gap_tot=gap_bad=0
puretravel_tot=puretravel_bad=0
worst=[]
for (e,dl,k,L),lt in dist.items():
    if lt >= DEPTH: continue          # frontier may be non-optimal-complete
    lr = LL.relaxed_solve(e,dl,k,L)
    d = lt - lr
    if d < 0 or d % 2: 
        worst.append(("PARITY/NEG",e,dl,k,L,lt,lr)); continue
    c = d//2
    ge = gap_edges(k,L)
    A = dict(L)
    supp_in_Ik = all(fvec(k,j)!=0 for j,v in A.items() if v!=0)
    if supp_in_Ik:
        puretravel_tot+=1
        if c!=0: puretravel_bad+=1
    if not ge:
        nogap_tot+=1
        if c!=0:
            nogap_bad+=1
            if len(worst)<6: worst.append(("NOGAP but c>0",e,dl,k,L,lt,lr,c))
    else:
        gap_tot+=1
        if c==0: gap_bad+=1

print(f"pure-travel (supp in I_k): {puretravel_tot} elements, violations (c!=0): {puretravel_bad}")
print(f"NO-GAP  : {nogap_tot} elements, violations (c!=0): {nogap_bad}")
print(f"HAS-GAP : {gap_tot} elements, of which c==0: {gap_bad}  ({100*gap_bad/max(gap_tot,1):.1f}%)")
for w in worst[:6]: print("  ", w)
