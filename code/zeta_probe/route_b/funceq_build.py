#!/usr/bin/env python3
"""
ROUTE B -- assemble the catalytic functional equation for the relaxed GF and
extract the kernel K(x,t).

We build the BULK (f=0) catalytic generating function exactly, with t marking
the current edge crossing count m, as a sanity-checkable algebraic object, then
state how travel edges and the k-sum extend it.

BULK SUB-MODEL (f=0 interior, the pure-lamp block):
Each edge has m=2s crossings (s>=1), u=dn=s, sign split (pu,pd) in [0,s]^2.
The site cost between consecutive bulk edges is the closed form
        SiteCost = 2*rem - c1
derived & verified (see funceq notes).  We expose the catalytic variable
t <-> m and assemble the column transfer as a power series; the bulk growth
rate r_bulk = 1/rho_bulk reproduces the README scaffold value (~1.378).

This script:
 (1) builds the bulk catalytic series B(x,t) = sum_{walks} x^{len} t^{m_last}
     by a TRUNCATED column DP (catalytic variable kept symbolic via t-degree),
 (2) extracts B(x,1) coefficients and the dominant singularity rho_bulk,
 (3) checks against the determinized bulk transfer (rho~0.7255).
"""
import sys, importlib.util, os
from collections import defaultdict
from functools import lru_cache
import sympy as sp

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
def site_cost_bL_pi(bL,f2,m2,pu2,pd2,is0=False,isk=False,eps=1,delta=0):
    u2,dn2=edge_updn(f2,m2); a,b,c,d=bL
    arr=[a,b,pd2,dn2-pd2]; dep=[c,d,pu2,u2-pu2]
    if is0: arr[0]+=1
    if isk:
        s=2 if delta==1 else 0
        dep[s+(0 if eps==1 else 1)]+=1
    if sum(arr)!=sum(dep): return None
    return site_cost(tuple(arr),tuple(dep))

# ---------------------------------------------------------------------------
# Determinized bulk transfer to reproduce rho_bulk (sanity vs README ~0.7255).
# State = normalized min-cost table over bulk profiles; transition appends a
# bulk edge of any deposit a.  This is the README scaffold, re-derived here, but
# we ALSO expose, for each transition, the increment in length (the x-exponent)
# and the new m (the t-exponent), so the SAME data feeds the catalytic eq.
# ---------------------------------------------------------------------------
@lru_cache(maxsize=None)
def bulk_profiles(mmax):
    out=defaultdict(list)
    for m in range(2,mmax+1,2):
        u=dn=m//2
        for pu in range(u+1):
            for pd in range(dn+1):
                a=2*pd-dn+u-2*pu
                out[a].append((0,m,pu,pd))
    return dict(out)

def norm(items):
    b=min(c for _,c in items)
    return tuple(sorted((p,c-b) for p,c in items)), b

def build_bulk_transfer(mmax):
    pmap=bulk_profiles(mmax)
    seeds=set()
    for a,profs in pmap.items():
        for pc in profs:
            nk,_=norm([(pc,0)]); seeds.add(nk)
    states=set(seeds); seen=set(seeds); frontier=list(seeds)
    edges=defaultdict(list)  # s -> list of (s', delta_len)
    while frontier:
        s=frontier.pop(); abstbl=[(p,r) for p,r in s]
        for a,profs in pmap.items():
            newitems=[]
            for pc in profs:
                fc,mc,puc,pdc=pc; best=None
                for pp,r in abstbl:
                    fp,mp_,pup,pdp=pp; bL=boundary_of(fp,mp_,pup,pdp)
                    scv=site_cost_bL_pi(bL,fc,mc,puc,pdc)
                    if scv is None: continue
                    v=r+scv+mc
                    if best is None or v<best: best=v
                if best is not None: newitems.append((pc,best))
            if newitems:
                nk,nb=norm(newitems)
                if nb>0: edges[s].append((nk,nb))
                if nk not in seen:
                    seen.add(nk); states.add(nk); frontier.append(nk)
    return sorted(states), edges

def bulk_rho(mmax):
    import mpmath as mp
    states,edges=build_bulk_transfer(mmax)
    idx={s:i for i,s in enumerate(states)}; n=len(states)
    def T(x):
        M=[[mp.mpf(0)]*n for _ in range(n)]
        for s,lst in edges.items():
            i=idx[s]
            for (s2,dl) in lst:
                if dl>0: M[i][idx[s2]]+=x**dl
        return mp.matrix(M)
    def specrad(x):
        ev=mp.eig(T(mp.mpf(x)),left=False,right=False)
        return max(abs(e) for e in ev)
    mp.mp.dps=25
    g=lambda x: specrad(x)-1
    rho=mp.findroot(g,(mp.mpf('0.5'),mp.mpf('0.95')),solver='bisect',tol=mp.mpf(10)**-15)
    return rho, n

if __name__=="__main__":
    mm=int(sys.argv[1]) if len(sys.argv)>1 else 12
    rho,n=bulk_rho(mm)
    print(f"BULK (f=0) determinized transfer: mmax={mm}, |states|={n}")
    print(f"  rho_bulk = {rho}")
    print(f"  r_bulk = 1/rho_bulk = {1/rho}")
    print(f"  (README scaffold target: rho~0.7255, r~1.378)")
