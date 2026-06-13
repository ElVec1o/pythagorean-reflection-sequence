#!/usr/bin/env python3
# Transfer-matrix / kernel approach to the EXACT growth rate r of the relaxed model.
# Bulk (f=0) profiles p=(m,pu,pd) with 0<=pu<=u, 0<=pd<=dn, u=dn=m/2 (f=0 => up=dn=m/2).
# Wait: f=0 => u=(m+0)/2=m/2, dn=m/2, so m even. up-strands=m/2, down-strands=m/2.
# Transition p->p' weighted by x^{m'/?}... cost added when moving to edge with
# profile p' = (crossings m' contributes m') + (site cost between p and p').
# Generating function of bulk walks: V(x) ~ sum over walks of x^{total cost}.
# Growth: r = 1/rho, rho = smallest x>0 with spectralRadius(T(x))=1, where
#   T(x)[p,p'] = x^{ m' + sitecost(p->p') }   (m' = crossings of the new edge).
# We INCLUDE the per-edge crossing cost on the destination edge; the site cost
# couples them. This is the bulk transfer of the same DP, WITHOUT min (counting).
#
# BUT: counting distinct ELEMENTS requires the deposit a_j to vary; in the bulk
# each profile p'=(m',pu',pd') corresponds to a specific a' = 2pd'-dn'+u'-2pu'
# = 2pd' - m'/2 + m'/2 - 2pu' = 2(pd'-pu').  So a' even, ranges over 2*(pd'-pu').
# Different (pu',pd') with same a' are DIFFERENT internal sign-arrangements but
# SAME element coefficient a'. For COUNTING ELEMENTS, the element is determined by
# the a-sequence; the (pu,pd) are auxiliary minimization variables. So the proper
# growth object must take the MIN over (pu,pd) per a-sequence -- not a linear
# transfer. This is why the min makes it a (min,+) / tropical problem.
#
# HOWEVER: the COUNTING generating function V(x)=sum v_n x^n is what we want, and
# v_n counts a-sequences at their MIN length. The determinized DP computes exactly
# this. Its transfer is over DETERMINIZED states (min-cost tables), which is the
# correct linear transfer for COUNTING. So: build the determinized-state transfer
# matrix B where B[s,s'] = (number of a_j letters causing s->s', tracked by the
# length increment). Then V(x) growth = dominant eigenvalue structure of B(x).
#
# We extract B(x) empirically: run the determinized DP in the BULK (f=0,
# is0=isk=False) and record, for each determinized state s and each a_j letter,
# the successor state s' and the cost increment delta. Then T(x)[s,s'] += x^delta.
# r = 1/rho with rho = min x>0 : specrad(T(x))=1.
import sys
_ARGV=list(sys.argv)
exec(open("/tmp/wf2_dp3.py").read().split('if __name__')[0])
from collections import defaultdict
import mpmath as mp

MMAX=int(_ARGV[1]) if len(_ARGV)>1 else 8

# Build bulk determinized transition graph. State = normalized cost table over
# bulk profiles. Start from all reachable states by BFS in the bulk.
def norm(items):
    b=min(c for _,c in items)
    return tuple(sorted((p,c-b) for p,c in items)), b

EMPTYP=(0,0,0,0)
fj=0; is0=False; isk=False; eps=1; delta=0  # bulk, no markers
profmap=all_profiles(fj,MMAX)

# successor of a determinized state under letter aj, with cost increment.
# state key = tkey (normalized table, base implicitly 0 since bulk shift-invariant)
def step(tkey, aj):
    abstbl=[(p,r) for p,r in tkey]
    profs=profmap.get(aj,[])
    newitems=[]
    for pc in profs:
        mcur=pc[1]; best=None
        for pp,cp in abstbl:
            # bulk: no reachability boundary constraints (j in interior). The
            # chain constraints in formula_len are about the START region; in a
            # pure bulk of nonzero activity all m>0. We require m>0 transitions.
            sc=sc_cached(pp,pc,is0,isk,eps,delta)
            if sc is None: continue
            v=cp+sc+mcur
            if best is None or v<best: best=v
        if best is not None: newitems.append((pc,best))
    if not newitems: return None
    nk,nb=norm(newitems)
    return nk, nb  # nb = cost increment (delta length)

# BFS reachable bulk states from the "single active strand" seed.
# seed: a table with one profile of minimal m (m=2 for f=0). Start broadly: all
# profiles with m in {2,..} as singletons.
seeds=set()
for aj,profs in profmap.items():
    for pc in profs:
        if pc[1]>0:
            tk,_=norm([(pc,0)])
            seeds.add(tk)
states=set(seeds)
edges=defaultdict(list)  # (s)->list of (s', delta)
frontier=list(seeds); seen=set(seeds)
while frontier:
    s=frontier.pop()
    for aj in profmap:
        res=step(s,aj)
        if res is None: continue
        s2,delta=res
        edges[s].append((s2,delta))
        if s2 not in seen:
            seen.add(s2); states.add(s2); frontier.append(s2)
states=sorted(states)
idx={s:i for i,s in enumerate(states)}
n=len(states)
print(f"# bulk determinized states (MMAX={MMAX}): {n}")
# transition multiplicities by delta
# T(x)[i,j] = sum over edges i->j of x^delta
def Tmat(x):
    M=[[mp.mpf(0)]*n for _ in range(n)]
    for s,lst in edges.items():
        i=idx[s]
        for (s2,delta) in lst:
            if delta==0: continue   # exclude m=0 "skip" transitions (no advance)
            M[i][idx[s2]]+=x**delta
    return M

def specrad(M):
    A=mp.matrix(M)
    ev=mp.eig(A, left=False, right=False)
    return max(abs(e) for e in ev)

# find rho: smallest x>0 with specrad(T(x))=1. specrad increases with x.
# bisect on x in (0,1).
def g(x): return specrad(Tmat(mp.mpf(x)))-1
mp.mp.dps=30
lo,hi=mp.mpf('0.01'),mp.mpf('0.99')
# ensure sign change
glo,ghi=g(lo),g(hi)
print(f"# g(0.01)={mp.nstr(glo,6)} g(0.99)={mp.nstr(ghi,6)}")
if glo*ghi<0:
    rho=mp.findroot(g,(lo,hi),solver='bisect',tol=mp.mpf(10)**-20)
    print(f"rho = {mp.nstr(rho,20)}")
    print(f"r = 1/rho = {mp.nstr(1/rho,20)}")
else:
    print("# no sign change in [0.01,0.99]; scanning")
    import numpy as np
    for xv in [0.05*i for i in range(1,20)]:
        print(f"  x={xv:.2f} specrad={mp.nstr(specrad(Tmat(mp.mpf(xv))),8)}")
