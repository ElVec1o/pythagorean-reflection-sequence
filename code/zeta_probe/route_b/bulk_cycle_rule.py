# Determine the per-edge cycle-creation rule for a PURE BULK run (k=0).
# At k=0 the single marker site is 0 (start+end). A bulk run is a sequence of even
# deposits on edges to one side. We enumerate runs and read off c(g) = (tl-rl)/2 to find
# the combinatorial rule generating cycles, so we can write the cycle-weighted FE.
import sys, os
import lamp_lib as LL
import importlib.util
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

# Right-side pure bulk run at k=0: deposits on edges 0,1,2,... (sites 0,1,2,...).
# Each edge j gets even deposit a_j in {.., -4,-2,2,4,..} or 0 (gap). Edge 0 touches the
# marker site 0. We enumerate small runs: edges 0..L-1 with deposits, read c.
# Goal: express c as a function of the deposit pattern (positions of nonzeros / gaps).
print("k=0, eps=1, dl=0, RIGHT run on edges 0..: c=(tl-rl)/2 vs deposit pattern")
print("pattern = tuple of (edge, a). Looking for: c = number of 'gap edges' before a nonzero?")
import itertools
def c_of(a):
    rl=relaxed_len(1,0,0,a); tl=LL.solve(1,0,0,a)
    if rl is None or tl is None: return None,rl,tl
    return (tl-rl)//2, rl, tl

# single deposit at edge e (e>=0): how many gaps (edges 0..e-1 empty) -> c?
print("\nSingle deposit a=2 at edge e (edges 0..e-1 are gaps):")
for e in range(0,7):
    c,rl,tl=c_of({e:2})
    # count gap edges strictly between marker site 0 and this deposit
    print(f"  e={e}: gaps_before={e}  c={c} (rl={rl},tl={tl})")

print("\nSingle deposit a=2 at edge e on the LEFT (edge -e-1, i.e. sites -e-1..0):")
for e in range(0,7):
    edge=-e-1
    c,rl,tl=c_of({edge:2})
    print(f"  edge={edge}: gaps_before={e}  c={c} (rl={rl},tl={tl})")

print("\nTwo deposits, right side, at edges e1<e2, contiguous vs gapped:")
for e1 in range(0,3):
    for e2 in range(e1+1,5):
        c,rl,tl=c_of({e1:2,e2:2})
        gaps_mid=e2-e1-1
        print(f"  edges {e1},{e2}: gaps_before_e1={e1} gaps_between={gaps_mid} c={c}")

print("\nDeposit magnitude effect: single deposit a=2m at edge 2 (2 gaps before):")
for m in range(1,4):
    c,rl,tl=c_of({2:2*m})
    print(f"  a={2*m} at edge2: c={c} (rl={rl},tl={tl})")
