#!/usr/bin/env python3
# Optimized relaxed counting DP: iterate over edge PROFILES directly (each
# profile fixes a_j), avoiding empty a_j branches. Same semantics as wf2_dp2.
import sys, importlib.util
spec=importlib.util.spec_from_file_location(
    "lf","/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe/lamp_formula.py")
lf=importlib.util.module_from_spec(spec); sys.argv=["lf","0"]; spec.loader.exec_module(lf)
site_cost=lf.site_cost
from collections import defaultdict
from functools import lru_cache

def edge_updn(f,m): return (m+f)//2,(m-f)//2

def sc_site(pp,cp,is0,isk,eps,delta):
    fp,mp_,pup,pdp=pp; fc,mc,puc,pdc=cp
    up,dnp=edge_updn(fp,mp_); uc,dnc=edge_updn(fc,mc)
    arr=[0,0,0,0]; dep=[0,0,0,0]
    arr[0]+=pup; arr[1]+=up-pup; arr[2]+=pdc; arr[3]+=dnc-pdc
    dep[0]+=pdp; dep[1]+=dnp-pdp; dep[2]+=puc; dep[3]+=uc-puc
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

EMPTY=('E',0,0,0)  # f-tag 'E' replaced by 0,m=0
EMPTYP=(0,0,0,0)

@lru_cache(maxsize=None)
def all_profiles(fj,mmax):
    # returns dict: aj -> list of profiles (fj,m,pu,pd)
    out=defaultdict(list)
    for m in range(0,mmax+1):
        if m==0 and fj!=0: continue
        if (m-fj)%2!=0: continue   # m must match f's parity (u,dn integral)
        u,dn=edge_updn(fj,m)
        if u<0 or dn<0: continue
        for pu in range(u+1):
            for pd in range(dn+1):
                aj=2*pd-dn+u-2*pu
                if m==0 and aj!=0: continue
                out[aj].append((fj,m,pu,pd))
    return dict(out)

@lru_cache(maxsize=None)
def sc_cached(pp,cp,is0,isk,eps,delta):
    return sc_site(pp,cp,is0,isk,eps,delta)

def slice_poly(eps,delta,k,JLO,JHI,mmax,Ncap):
    def norm(items):
        b=min(c for _,c in items)
        return tuple(sorted((p,c-b) for p,c in items)), b
    states=defaultdict(int)
    states[((((EMPTYP,0),)),0)]=1  # table {EMPTYP:0}, base 0 ; store normalized
    # represent state key as (tkey,base): tkey=tuple((profile,rel)), here EMPTYP rel0
    states=defaultdict(int); states[(((EMPTYP,0),),0)]=1
    for j in range(JLO,JHI+1):
        fj=f_of(j,k); is0=(j==0); isk=(j==k)
        profmap=all_profiles(fj,mmax)
        nxt=defaultdict(int)
        for (tkey,base),cnt in states.items():
            abstbl=[(p,base+r) for p,r in tkey]
            for aj,profs in profmap.items():
                newitems=[]
                for pc in profs:
                    mcur=pc[1]; best=None
                    for pp,cp in abstbl:
                        pm=pp[1]
                        if j<=-1 and pm>0 and mcur==0: continue
                        if j>=1 and pm==0 and mcur>0: continue
                        sc=sc_cached(pp,pc,is0,isk,eps,delta)
                        if sc is None: continue
                        v=cp+sc+mcur
                        if best is None or v<best: best=v
                    if best is not None and best<=Ncap:
                        newitems.append((pc,best))
                if newitems:
                    nk,nb=norm(newitems)
                    nxt[(nk,nb)]+=cnt
        states=nxt
        if not states: break
    j=JHI+1; fj=f_of(j,k); is0=(j==0); isk=(j==k)
    poly=defaultdict(int)
    for (tkey,base),cnt in states.items():
        best=None
        for p,r in tkey:
            sc=sc_cached(p,EMPTYP,is0,isk,eps,delta)
            if sc is None: continue
            v=base+r+sc
            if best is None or v<best: best=v
        if best is not None: poly[best]+=cnt
    return poly

if __name__=="__main__":
    truth={(1,0,0):{0:1,6:4,8:4,10:16},(1,1,0):{1:1,5:2,7:2,9:9},
           (1,0,1):{2:1,4:1,6:1,8:7,10:8},(-1,0,0):{2:1,4:1,6:2,8:3,10:11},
           (1,0,2):{4:2,6:2,8:2,10:16},(1,1,1):{3:2,7:4,9:6}}
    for key,exp in truth.items():
        eps,delta,k=key
        poly=slice_poly(eps,delta,k,min(0,k)-6,max(0,k)+6,6,10)
        ok=all(poly.get(n,0)==exp.get(n,0) for n in range(0,11))
        print(f"{key}: {'OK' if ok else 'BAD'} {[poly.get(n,0) for n in range(0,11)]}")
