# Proper test of k-independence. Travel interval [0,k), k>=1: those edges carry f=+1 and
# must have ODD deposits (or be omitted -> a default odd deposit a=+1 = minimal travel edge).
# Bulk deposits are EVEN, at edges OUTSIDE [0,k).
# We attach a fixed RIGHT bulk run at edges >= k (gap-edges past the travel endpoint k),
# and check c as a function of (r = how far past k) independent of k.
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

def make(eps,dl,k,bulk):
    # travel edges 0..k-1 get a=+1 (minimal odd, consistent with f=+1)
    a=dict(bulk)
    for j in range(0,k):
        a[j]=1   # odd deposit on travel edge (f=+1): a and f same parity OK
    return a

print("Right bulk run: single even deposit a=+2 at edge (k-1+r), r gap-edges PAST travel end k.")
print("(travel edges 0..k-1 carry a=+1). vary k, fixed r.")
for r in [1,2,3]:
    print(f" r={r}:")
    for k in range(1,6):
        edge=k-1+r   # edge index; site k is travel end. edges>=k are bulk. edge=k-1+r => for r>=1, edge>=k
        bulk={edge:2}
        a=make(1,0,k,bulk)
        rl=relaxed_len(1,0,k,a)
        tl=LL.solve(1,0,k,a)
        if rl is None or tl is None:
            print(f"   k={k}: edge={edge} infeasible (rl={rl},tl={tl})"); continue
        c=(tl-rl)//2
        print(f"   k={k}: edge={edge} a={a} rl={rl} tl={tl} c={c}")
