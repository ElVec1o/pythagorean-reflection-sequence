# Decisive test: c(g) = (cycles from LEFT bulk run) + (cycles from RIGHT bulk run),
# INDEPENDENT of travel length |k|.  We construct elements with a fixed RIGHT bulk run
# attached at site k (deposits at edges >= k), no left run, varying k, and check c is
# constant once |k| is large enough that the run is fully to the right of the spine.
#
# Concretely: place a single even deposit at edge (k + r) for r>=1 (r gap-edges past the
# spine endpoint k), k ranging. If c depends only on r (not on k), the travel block is inert.
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def truelen_via_bfs_consistent(eps,dl,k,a):
    # use the exact connectivity solver (slow but correct) for these specific elements
    return LL.solve(eps,dl,k,dict(a))

print("Test A: single deposit a=+2 at edge (k+r), eps=1, dl=0, vary k>=0, r in {1,2,3}")
for r in [1,2,3]:
    print(f" r={r} (gap-edges past spine-right):")
    for k in range(0,6):
        edge=k+r
        a={edge:2}
        rl=relaxed_len(1,0,k,a)
        tl=LL.solve(1,0,k,a)
        if rl is None or tl is None:
            print(f"   k={k}: infeasible"); continue
        c=(tl-rl)//2
        print(f"   k={k}: edge={edge} rl={rl} tl={tl} c={c}")
print()
print("Test B: deposit a=+2 at edge -(r) to the LEFT of site 0, with travel to the right (k>=0)")
for r in [1,2,3]:
    print(f" r={r} (gap-edges left of site 0):")
    for k in range(0,6):
        edge=-r  # left of 0
        a={edge:2}
        rl=relaxed_len(1,0,k,a)
        tl=LL.solve(1,0,k,a)
        if rl is None or tl is None:
            print(f"   k={k}: infeasible"); continue
        c=(tl-rl)//2
        print(f"   k={k}: edge={edge} rl={rl} tl={tl} c={c}")
print()
print("Test C: BOTH a left deposit at edge -1 AND a right deposit at edge k+1, vary k")
for k in range(0,6):
    a={-1:2, k+1:2}
    rl=relaxed_len(1,0,k,a)
    tl=LL.solve(1,0,k,a)
    if rl is None or tl is None:
        print(f"   k={k}: infeasible"); continue
    c=(tl-rl)//2
    print(f"   k={k}: a={a} rl={rl} tl={tl} c={c}")
