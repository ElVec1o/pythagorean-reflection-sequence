#!/usr/bin/env python3
"""
Census the BOUNDED catalytic state space: the rightmost-edge boundary class
MODULO the catalytic crossing-count m.

Key idea (the corrected lemma from the shape analysis): in a length-minimizing
relaxed realization each interface component carries <=1 up-crossing and <=1
down-crossing of each edge => 8-shape alphabet, with the bulk MULTIPLICITY being
the catalytic variable.  So the boundary datum that matters for the next site
cost, ONCE m is the catalytic mark, is bounded: it is the (side,sign) content of
the rightmost edge's strands COMPRESSED to its 4-vector of TYPE-PRESENCE/parity,
not the raw counts.

Here we test the minimal sufficient compression: the boundary class is
b=(up+,up-,dn+,dn-) counts, but in an OPTIMAL sweep these counts are themselves
governed by m via u=(m+f)/2, dn=(m-f)/2, and the only free choices are pu,pd.
The catalytic claim is: the per-site MIN cost depends on (bL,profile') only
through a BOUNDED summary of bL.  We verify this by computing, for the determin-
ized DP, the partition of boundary classes into "cost-equivalence classes":
two boundary classes bL,bL' are equivalent iff for EVERY appended profile pi'
(over all f',m'<=mmax,pu',pd') the site cost agrees.  Count those classes.
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

def site_cost_bL_pi(bL,f2,m2,pu2,pd2):
    u2,dn2=edge_updn(f2,m2); up_p,up_m,dn_p,dn_m=bL
    arr=(up_p,up_m,pd2,dn2-pd2); dep=(dn_p,dn_m,pu2,u2-pu2)
    if sum(arr)!=sum(dep): return None
    return site_cost(arr,dep)

@lru_cache(maxsize=None)
def all_profiles(f,mmax):
    out=[]
    for m in range(0,mmax+1):
        if m==0 and f!=0: continue
        if (m-f)%2: continue
        u,dn=edge_updn(f,m)
        for pu in range(u+1):
            for pd in range(dn+1):
                out.append((f,m,pu,pd))
    return out

if __name__=="__main__":
    MMAX=int(sys.argv[1]) if len(sys.argv)>1 else 10
    # all boundary classes bL=(up+,up-,dn+,dn-) reachable from f in {-1,0,1},m<=mmax
    bset=set()
    for f in (-1,0,1):
        for (ff,m,pu,pd) in all_profiles(f,MMAX):
            u,dn=edge_updn(f,m); bset.add((pu,u-pu,pd,dn-pd))
    bset=sorted(bset)
    # appended-profile test set (right edges)
    rights=[]
    for f2 in (-1,0,1):
        rights+=all_profiles(f2,MMAX)
    # cost signature of each bL: tuple of site costs over all rights (None->'X')
    sig={}
    for bL in bset:
        s=tuple(site_cost_bL_pi(bL,*r) if site_cost_bL_pi(bL,*r) is not None else -1
                for r in rights)
        sig[bL]=s
    classes=defaultdict(list)
    for bL in bset: classes[sig[bL]].append(bL)
    print(f"mmax={MMAX}: #boundary classes={len(bset)}, "
          f"#cost-equivalence classes={len(classes)}")
    # show representative structure
    reps=sorted([min(v) for v in classes.values()])
    print("representatives (up+,up-,dn+,dn-):")
    for r in reps: print("   ",r)
    print("\nconvergence of #cost-equiv classes in mmax:")
    for mm in (4,6,8,10,12,14):
        bset2=set()
        for f in (-1,0,1):
            for (ff,m,pu,pd) in all_profiles(f,mm):
                u,dn=edge_updn(f,m); bset2.add((pu,u-pu,pd,dn-pd))
        rights2=[]
        for f2 in (-1,0,1): rights2+=all_profiles(f2,mm)
        cl=defaultdict(list)
        for bL in bset2:
            s=tuple(site_cost_bL_pi(bL,*r) if site_cost_bL_pi(bL,*r) is not None else -1 for r in rights2)
            cl[s].append(bL)
        print(f"  mmax={mm}: #boundary={len(bset2)}  #cost-classes={len(cl)}")
