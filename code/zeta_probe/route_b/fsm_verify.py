#!/usr/bin/env python3
"""
fsm_verify.py -- Recast the closed form c_pred (c_formula.py) as an EXPLICIT
left-to-right Mealy transducer reading each side of the spine outward, and CERTIFY
that the explicit FSM reproduces c_pred exactly (so the transition table that gets
typeset in the paper is faithful, making the Part-B lower bound checkable on paper).

Side transducer (read positions outward from the spine endpoint):
  state = (seen_block: bool, shield_avail: 0/1)
  init  : seen_block=False, shield_avail = shield0   (shield0 = boundary shield of this side)
  on DEPOSIT edge : emit 0 ; seen_block=True ; shield_avail=1   (reset: inner runs shield 1)
  on GAP edge     : if shield_avail>0: emit 0; shield_avail-=1   else: emit +1
  (read only out to the outermost deposit; no trailing gap exists since the active
   span ends at the outermost active edge.)
Total c_FSM = right_emit + left_emit + boundary_correction(e,dl,k,a).
"""
import os, sys, importlib.util, random
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("c_formula", os.path.join(HERE, "c_formula.py"))
CF = importlib.util.module_from_spec(spec); sys.argv=["c_formula"]; spec.loader.exec_module(CF)
f_of, sgn = CF.f_of, CF.sgn
shield_right, shield_left = CF.shield_right, CF.shield_left
c_pred, boundary_correction = CF.c_pred, CF.boundary_correction

def side_emit(positions_outward, is_deposit, shield0):
    """Run the side Mealy machine over the positions (already ordered OUTWARD),
    truncated at the outermost deposit. Returns total emitted cost."""
    # truncate trailing gaps past the last deposit
    last_dep = max((i for i,p in enumerate(positions_outward) if is_deposit(p)), default=-1)
    if last_dep < 0: return 0
    seen_block, shield_avail, total = False, shield0, 0
    for p in positions_outward[:last_dep+1]:
        if is_deposit(p):
            seen_block = True; shield_avail = 1   # emit 0
        else:
            if shield_avail > 0: shield_avail -= 1  # emit 0 (shielded)
            else: total += 1                        # emit +1
    return total

def c_fsm(eps, dl, k, a):
    a = {j:v for j,v in a.items() if v}
    spineL, spineR = min(0,k), max(0,k)
    sR = a.get(k-1,0) if k>0 else (a.get(-1,0) if k<0 else 0)
    sL = a.get(k,0)   if k<0 else 0
    nz = set(a)
    def dep_right(p): return (p in nz) and f_of(p,k)==0
    def dep_left(p):  return (p in nz) and f_of(p,k)==0
    # RIGHT: positions spineR, spineR+1, ... outward
    if nz:
        hi = max(nz); lo = min(nz)
    else:
        hi = spineR; lo = spineL
    right_pos = list(range(spineR, hi+1))
    cR = side_emit(right_pos, dep_right, shield_right(k,eps,dl,sR))
    # LEFT: positions spineL-1, spineL-2, ... outward (decreasing)
    left_pos = list(range(spineL-1, lo-1, -1))
    cL = side_emit(left_pos, dep_left, shield_left(k,eps,dl,sL))
    return cR + cL + boundary_correction(eps,dl,k,a)

# ---- A) certify against c_pred on the BFS-reachable elements ----
def test_bfs(D):
    import lamp_lib as LL
    cf = importlib.util.module_from_spec(
        importlib.util.spec_from_file_location("cat", os.path.join(HERE,"catalytic_funceq.py")))
    sys.argv=["cat","0"]; cf.__spec__.loader.exec_module(cf)
    rl = cf.relaxed_len_local
    dist = LL.bfs(D); n=0; mis=0
    for (e,dl,k,L),d in dist.items():
        a=dict(L)
        if rl(e,dl,k,a) is None: continue
        n+=1
        if c_fsm(e,dl,k,a) != c_pred(e,dl,k,a): mis+=1
    print(f"[BFS depth {D}] {n} elements, FSM vs c_pred mismatches: {mis}")
    return mis

# ---- B) stress: random arbitrary profiles (unbounded gaps/magnitudes) ----
def test_random(N, seed=12345):
    rnd = random.Random(seed); mis=0; examples=[]
    for _ in range(N):
        k = rnd.randint(-6,6); eps = rnd.choice([1,-1]); dl = rnd.randint(0,1)
        spineL, spineR = min(0,k), max(0,k)
        a={}
        # travel edges carry odd nonzero
        for p in range(spineL, spineR):
            a[p] = rnd.choice([-3,-1,1,3,5])
        # off-spine positions in a wide window: 0 (gap) or a deposit
        for p in list(range(spineL-9, spineL)) + list(range(spineR, spineR+9)):
            a[p] = rnd.choice([0,0,0,2,-2,1,-1,4,-4,3,-3])
        if c_fsm(eps,dl,k,a) != c_pred(eps,dl,k,a):
            mis+=1
            if len(examples)<8: examples.append((eps,dl,k,dict(a),c_fsm(eps,dl,k,a),c_pred(eps,dl,k,a)))
    print(f"[random {N}] FSM vs c_pred mismatches: {mis}")
    for ex in examples: print("   MISMATCH", ex)
    return mis

if __name__=="__main__":
    D = int(sys.argv[1]) if len(sys.argv)>1 else 14
    m1 = test_bfs(D)
    m2 = test_random(200000)
    print("CERTIFIED FAITHFUL" if (m1==0 and m2==0) else "*** FSM DIVERGES FROM c_pred ***")
