#!/usr/bin/env python3
"""
Find the MINIMAL boundary feature set that makes shieldTot = (GL+GR) - c_true deterministic.
GL,GR = detour gap edges on each side. If shieldTot is a well-defined function of a small
boolean/sign feature tuple, that IS the exact closed-form shield law.
"""
import sys,os,importlib.util
from collections import defaultdict
import lamp_lib as LL
HERE=os.path.dirname(os.path.abspath(__file__))
def load(mod,path):
    sv=list(sys.argv);spec=importlib.util.spec_from_file_location(mod,os.path.join(HERE,path))
    m=importlib.util.module_from_spec(spec);sys.argv=[mod,'0'];spec.loader.exec_module(m);sys.argv=sv;return m
cf=load('cf','catalytic_funceq.py'); rl=cf.relaxed_len_local
def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)
def sgn(x): return 1 if x>0 else(-1 if x<0 else 0)

def feats(e,dl,k,a):
    a={j:v for j,v in a.items() if v}; nz=sorted(a)
    sL=min(0,k); sR=max(0,k)
    R=[p for p in nz if p>=sR and f_of(p,k)==0]
    L=[p for p in nz if p+1<=sL and f_of(p,k)==0]
    GR=sum(1 for j in range(sR,max(R)) if a.get(j,0)==0 and f_of(j,k)==0) if R else 0
    GL=sum(1 for j in range(min(L)+1,sL) if a.get(j,0)==0 and f_of(j,k)==0) if L else 0
    kc = sgn(k)
    sRt = sgn(a.get(k-1,0)) if k>0 else (sgn(a.get(-1,0)) if k<0 else 0)  # right spine travel-dep sign
    sLt = sgn(a.get(k,0)) if k<0 else 0                                   # left spine travel-dep sign
    adjR = sgn(a.get(sR,0))   if f_of(sR,k)==0   else 0   # SIGN of even deposit glued right of spine
    adjL = sgn(a.get(sL-1,0)) if f_of(sL-1,k)==0 else 0    # SIGN of even deposit glued left of spine
    return dict(GL=GL,GR=GR,hasL=int(bool(L)),hasR=int(bool(R)),kc=kc,e=e,dl=dl,
                sRt=sRt,sLt=sLt,adjR=adjR,adjL=adjL)

def main():
    D=int(sys.argv[1]) if len(sys.argv)>1 else 16
    dist=LL.bfs(D)
    # try increasing feature sets; report determinism + the table
    keysets={
      'A: e,dl,kc,hasL,hasR': ('e','dl','kc','hasL','hasR'),
      'B: +adjL,adjR':        ('e','dl','kc','hasL','hasR','adjL','adjR'),
      'C: +sRt,sLt':          ('e','dl','kc','hasL','hasR','adjL','adjR','sRt','sLt'),
    }
    data=[]
    for (e,dl,k,Lp),d in dist.items():
        a=dict(Lp); r=rl(e,dl,k,a)
        if r is None: continue
        c=(d-r)//2; F=feats(e,dl,k,a)
        sh=F['GL']+F['GR']-c
        data.append((F,sh,(e,dl,k,a),c))
    for name,ks in keysets.items():
        groups=defaultdict(set)
        for F,sh,_,_ in data: groups[tuple(F[x] for x in ks)].add(sh)
        nbad=sum(1 for v in groups.values() if len(v)>1)
        print(f"{name}: {len(groups)} cells, {nbad} NON-deterministic")
    # print the full table for set C, only cells that are deterministic, plus flag bad
    ks=keysets['C: +sRt,sLt']
    groups=defaultdict(list)
    for F,sh,elt,c in data: groups[tuple(F[x] for x in ks)].append((sh,elt,c))
    print("\n# Non-deterministic cells under C (need more features):")
    nb=0
    for key,vals in sorted(groups.items()):
        shs=set(v[0] for v in vals)
        if len(shs)>1:
            nb+=1
            if nb<=12:
                print("  ",dict(zip(ks,key)),"shieldTot in",sorted(shs))
                for sh,elt,c in vals[:4]: print("      ",elt,"c=",c,"sh=",sh)
    print(f"# total nondeterministic cells under C: {nb}")
if __name__=="__main__": main()
