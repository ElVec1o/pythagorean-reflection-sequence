#!/usr/bin/env python3
"""
Hunt for the GLOBAL Z2 invariant that closes c. Model:
    c_true = c_pred + E,   E in {-1,0,1}.
Find a single global bit b(g) such that E is a deterministic function of
(local cell, b).  Local cell = (e,dl,sgn k, hasLdet, hasRdet) where hasXdet = side X
has a DETOUR (G>=1).  Many candidate global bits tested; report which make E deterministic.
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

def gbits(e,dl,k,a):
    a={j:v for j,v in a.items() if v}; nz=sorted(a)
    vals=[a[j] for j in nz]
    evens=[a[j] for j in nz if a[j]%2==0]
    odds =[a[j] for j in nz if a[j]%2!=0]
    b={}
    b['suma']   = (sum(vals))%2
    b['sumabs'] = (sum(abs(v) for v in vals))%2
    b['nev']    = len(evens)%2
    b['ndep']   = len(nz)%2
    b['npos']   = sum(1 for v in vals if v>0)%2
    b['nneg']   = sum(1 for v in vals if v<0)%2
    b['kpar']   = k%2
    b['nevneg'] = sum(1 for v in evens if v<0)%2          # parity of # negative even blocks
    b['evhalf'] = (sum(v//2 for v in evens))%2
    b['noddneg']= sum(1 for v in odds if v<0)%2
    b['sumeven']= (sum(evens))%2 if evens else 0
    b['alt']    = sum(1 for i in range(len(vals)-1) if sgn(vals[i])!=sgn(vals[i+1]))%2
    b['eps']    = 0 if e==1 else 1
    # signed area: sum_j a_j * j  (a discrete moment) parity
    b['mom']    = (sum(a[j]*j for j in nz))%2
    return b

def main():
    D=int(sys.argv[1]) if len(sys.argv)>1 else 16
    dist=LL.bfs(D)
    rows=[]
    allbits=None
    for (e,dl,k,L),d in dist.items():
        a=dict(L); r=rl(e,dl,k,a)
        if r is None: continue
        ct=(d-r)//2; cp=C.c_pred(e,dl,k,a); E=ct-cp
        # local cell
        sL=min(0,k); sR=max(0,k); nz=[j for j in a if a[j]]
        Rdep=[p for p in nz if p>=sR and f_of(p,k)==0]
        Ldep=[p for p in nz if p+1<=sL and f_of(p,k)==0]
        GR=sum(1 for j in range(sR,max(Rdep)) if a.get(j,0)==0 and f_of(j,k)==0) if Rdep else 0
        GL=sum(1 for j in range(min(Ldep)+1,sL) if a.get(j,0)==0 and f_of(j,k)==0) if Ldep else 0
        cell=(e,dl,sgn(k),int(GL>=1),int(GR>=1),int(bool(Ldep)),int(bool(Rdep)))
        gb=gbits(e,dl,k,a); allbits=list(gb)
        rows.append((cell,gb,E,(e,dl,k,a),ct))
    nz=[r for r in rows if r[2]!=0]
    print(f"depth {D}: {len(rows)} elts, {len(nz)} with E!=0 ({100*len(nz)/len(rows):.2f}%). E values:",
          sorted(set(r[2] for r in rows)))
    # baseline: is E determined by cell alone?
    def determinism(keyfn):
        g=defaultdict(set)
        for cell,gb,E,elt,ct in rows: g[keyfn(cell,gb)].add(E)
        return sum(1 for v in g.values() if len(v)>1), len(g)
    nb,ng=determinism(lambda cell,gb: cell)
    print(f"cell alone: {nb}/{ng} cells nondeterministic")
    # try cell + each single global bit
    best=[]
    for name in allbits:
        nb,ng=determinism(lambda cell,gb: cell+(gb[name],))
        best.append((nb,name,ng))
    best.sort()
    print("cell + ONE global bit (fewest nondeterministic cells first):")
    for nb,name,ng in best[:8]:
        print(f"   +{name:8s}: {nb} nondet / {ng} cells")
    # try cell + pairs of bits for the top bit
    top=best[0][1]
    best2=[]
    for name in allbits:
        if name==top: continue
        nb,ng=determinism(lambda cell,gb: cell+(gb[top],gb[name]))
        best2.append((nb,name,ng))
    best2.sort()
    print(f"cell + {top} + ONE more bit:")
    for nb,name,ng in best2[:6]:
        print(f"   +{top}+{name:8s}: {nb} nondet / {ng} cells")
if __name__=="__main__": main()
