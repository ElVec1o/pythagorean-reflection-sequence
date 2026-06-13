#!/usr/bin/env python3
"""
Census the determinized boundary-state space of the relaxed catalytic DP.

The catalytic functional equation is algebraic via Bousquet-Melou--Jehanne iff
the underlying *determinized* boundary automaton has a FINITE state set (each
state = a normalized min-cost table over the finite profile alphabet, after the
shift-by-base used in determinization).  We enumerate, over all (eps,delta,k)
slices reachable within radius R, the set of normalized tables that occur as
boundary states, and report its size and structure.

If finite: the section-vector F = (F_q)_{q in Q} is finite-dimensional, the
transfer is a finite linear system in the catalytic variable t, and BMJ Thm 3
applies (one catalytic variable t, |Q| sections) => F(x,1) algebraic.
"""
import sys, importlib.util, os
from collections import defaultdict
from functools import lru_cache

HERE=os.path.dirname(os.path.abspath(__file__))
ZP=os.path.dirname(HERE)
_S=list(sys.argv)
spec=importlib.util.spec_from_file_location("lf",os.path.join(ZP,"lamp_formula.py"))
lf=importlib.util.module_from_spec(spec); sys.argv=["lf","0"]; spec.loader.exec_module(lf)
sys.argv=_S
site_cost=lf.site_cost

def edge_updn(f,m): return (m+f)//2,(m-f)//2
def boundary_of(f,m,pu,pd):
    u,dn=edge_updn(f,m); return (pu,u-pu,pd,dn-pd)
def site_increment(bL,f2,m2,pu2,pd2,is0,isk,eps,delta):
    u2,dn2=edge_updn(f2,m2); up_p,up_m,dn_p,dn_m=bL
    arr=[up_p,up_m,pd2,dn2-pd2]; dep=[dn_p,dn_m,pu2,u2-pu2]
    if is0: arr[0]+=1
    if isk:
        s=2 if delta==1 else 0
        dep[s+(0 if eps==1 else 1)]+=1
    if sum(arr)!=sum(dep): return None
    return site_cost(tuple(arr),tuple(dep))
def f_of(j,k):
    if 0<=j<k: return 1
    if k<=j<0: return -1
    return 0
@lru_cache(maxsize=None)
def profiles_by_a(f,mmax):
    out=defaultdict(list)
    for m in range(0,mmax+1):
        if m==0 and f!=0: continue
        if (m-f)%2: continue
        u,dn=edge_updn(f,m)
        if u<0 or dn<0: continue
        for pu in range(u+1):
            for pd in range(dn+1):
                a=2*pd-dn+u-2*pu
                if m==0 and a!=0: continue
                out[a].append((f,m,pu,pd))
    return dict(out)

# We census the BULK boundary automaton (f=0 interior) AND the travel automaton
# (f=+-1) separately, since the kernel splits into a lamp block and a travel
# block.  A determinized state is the normalized table over profiles, but for
# the TRANSFER it is enough to track the EQUIVALENCE CLASS under "which boundary
# class each min-cost entry maps to and its relative cost" -- i.e. the function
# q -> min relative cost to leave with boundary class q'.  We census the raw
# normalized tables to upper-bound |Q|.

def norm(items):
    b=min(c for _,c in items)
    return tuple(sorted((p,c-b) for p,c in items)), b

def census(fseq_type, mmax, depth):
    """fseq_type: 'bulk' (all f=0), 'travelL' (f=+1), 'travelR' (f=-1).
    BFS the determinized boundary states reachable by appending edges of the
    given f, recording the set of normalized tables (the catalytic state)."""
    f = 0 if fseq_type=='bulk' else (1 if fseq_type=='travelL' else -1)
    pmap=profiles_by_a(f,mmax)
    EMPTYP=(0,0,0,0)
    # seeds: single-profile tables (any profile with m>0)
    seeds=set()
    for a,profs in pmap.items():
        for pc in profs:
            if pc[1]>0:
                nk,_=norm([(pc,0)]); seeds.add(nk)
    seen=set(seeds); frontier=list(seeds)
    # transitions: from table tkey, choose deposit a, get new table over profiles
    # of that a, with cost = min over old entry + site + new m.
    steps=0
    while frontier and steps<depth*len(seen)+10000:
        tkey=frontier.pop(); steps+=1
        abstbl=[(p,r) for p,r in tkey]
        for a,profs in pmap.items():
            newitems=[]
            for pc in profs:
                fc,mc,puc,pdc=pc; best=None
                for pp,r in abstbl:
                    fp,mp_,pup,pdp=pp
                    bL=boundary_of(fp,mp_,pup,pdp)
                    sc=site_increment(bL,fc,mc,puc,pdc,False,False,1,0)
                    if sc is None: continue
                    v=r+sc+mc
                    if best is None or v<best: best=v
                if best is not None: newitems.append((pc,best))
            if newitems:
                nk,_=norm(newitems)
                if nk not in seen:
                    seen.add(nk); frontier.append(nk)
    return seen

if __name__=="__main__":
    MMAX=int(sys.argv[1]) if len(sys.argv)>1 else 12
    for typ in ('bulk','travelL','travelR'):
        S=census(typ,MMAX,40)
        sizes=defaultdict(int)
        for tk in S: sizes[len(tk)]+=1
        print(f"{typ:8s} mmax={MMAX}: |Q|={len(S)} states; "
              f"table-size histogram (entries:count) = {dict(sorted(sizes.items()))}")
    # convergence check across mmax
    print("\nconvergence of |Q_bulk| in mmax:")
    for mm in (6,8,10,12,14,16):
        S=census('bulk',mm,40)
        print(f"  mmax={mm}: |Q_bulk|={len(S)}")
