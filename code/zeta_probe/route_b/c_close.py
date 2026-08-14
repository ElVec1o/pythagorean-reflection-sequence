#!/usr/bin/env python3
"""
Close c: c_full = c_pred(block/gap model) + boundary_correction(feature), where the
correction is a FINITE deterministic table keyed by O(1) boundary data. Build the table
from one depth, VALIDATE on held-out depths (different parity) -> if 0 mismatch, c is CLOSED.
"""
import sys,os,importlib.util
from collections import defaultdict
import lamp_lib as LL
HERE=os.path.dirname(os.path.abspath(__file__))
def load(m,p):
    sv=list(sys.argv);s=importlib.util.spec_from_file_location(m,os.path.join(HERE,p));x=importlib.util.module_from_spec(s);sys.argv=[m,'0'];s.loader.exec_module(x);sys.argv=sv;return x
cf=load('cf','catalytic_funceq.py'); rl=cf.relaxed_len_local
import c_formula as C
def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)
def sgn(x): return 1 if x>0 else(-1 if x<0 else 0)

def feat(e,dl,k,a):
    sL=min(0,k); sR=max(0,k); nz=sorted(a)
    Rev=[p for p in nz if p>=sR and f_of(p,k)==0]; Lev=[p for p in nz if p+1<=sL and f_of(p,k)==0]
    aLv = a[sL-1] if (Lev and max(Lev)==sL-1) else 0
    aRv = a[sR]   if (Rev and min(Rev)==sR)   else 0
    def cls(v): return (sgn(v), 1 if abs(v)>=4 else 0)
    return (e,dl,sgn(k),cls(aLv),cls(aRv),int(bool(Lev)),int(bool(Rev)))

def gather(D):
    dist=LL.bfs(D); rows=[]
    for (e,dl,k,L),d in dist.items():
        a={j:v for j,v in dict(L).items() if v}; r=rl(e,dl,k,a)
        if r is None: continue
        rows.append((feat(e,dl,k,a),(d-r)//2-C.c_pred(e,dl,k,a)))
    return rows

if __name__=="__main__":
    build_D=int(sys.argv[1]) if len(sys.argv)>1 else 22
    test_Ds=[int(x) for x in sys.argv[2:]] or [21,23]
    rows=gather(build_D)
    tab=defaultdict(lambda:defaultdict(int))
    for ft,E in rows: tab[ft][E]+=1
    # deterministic correction: the unique nonzero E in each cell (0 if all zero)
    corr={}; impure=0
    for ft,Es in tab.items():
        nz=[E for E in Es if E!=0]
        if len(set(nz))>1 or (nz and 0 in Es): impure+=1; corr[ft]=max(set(nz),key=lambda v:list(Es).count(v))
        elif nz: corr[ft]=nz[0]
    print(f"built table from depth {build_D}: {len(corr)} nonzero cells, {impure} IMPURE (should be 0)")
    for ft in sorted(corr): print("   ",ft,"->",corr[ft])
    # validate (held out)
    for D in test_Ds:
        tr=gather(D); n=len(tr); miss=0
        for ft,E in tr:
            if E-corr.get(ft,0)!=0: miss+=1
        print(f"  validate depth {D}: {miss}/{n} mismatch  ({'CLOSED' if miss==0 else 'residual'})")
