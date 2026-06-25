#!/usr/bin/env python3
"""
c_formula.py -- CANDIDATE closed form for the connectivity penalty c, so that
    true_geodesic_length(eps,dl,k,a) = relaxed_len_local(eps,dl,k,a) + 2*c_pred(eps,dl,k,a).

HYPOTHESIS (line-connectivity / Chinese-postman bridging with marker shield):
  Work in the edge span [LO,HI). An edge is ACTIVE if it carries a deposit (a_j!=0)
  or is a travel edge (f_j!=0). Inactive edges form maximal GAP-RUNS. The walker must
  physically bridge every gap-run separating a detached deposit block from the spine
  [min(0,k),max(0,k)]; each costs (g) extra crossings (c units), MINUS a shield of 1 if
  a marker sits on the spine-side of the run AND its connecting direction points into it:
    - start marker (site 0) connects DOWN/LEFT;
    - end marker  (site k) connects RIGHT iff dl==1, LEFT iff dl==0.
  Shield is capped at 1 per run (one excursion absorbs one direction).
"""
def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def sgn(x): return 1 if x>0 else (-1 if x<0 else 0)

def shield_right(k,e,dl,b):
    # b = SIGNED deposit on the travel edge adjacent to the RIGHT spine endpoint.
    if k==0: return 0 if (e==1 and dl==0) else 1   # no travel edge
    if abs(b)>=3: return 1            # thrice-crossed boundary edge always has a spare turn
    s=sgn(b)
    if k>0:  return 1 if dl==1 else (1 if s==e else 0)
    return 1 if s==-1 else 0          # k<0: START endpoint, b=a_{-1}

def shield_left(k,e,dl,b):
    # b = SIGNED deposit on the travel edge adjacent to the LEFT spine endpoint.
    if k>=0: return 1                 # START endpoint (site 0) connects left
    if abs(b)>=3: return 1
    return 1 if dl==0 else (0 if e==sgn(b) else 1)   # k<0: END endpoint at site k

def c_pred(eps,dl,k,a):
    a={j:v for j,v in a.items() if v}
    nz=sorted(a)
    spineL=min(0,k); spineR=max(0,k)
    # SIGNED boundary travel-edge deposits (travel edges always carry odd, nonzero a)
    sR = a.get(k-1,0) if k>0 else (a.get(-1,0) if k<0 else 0)
    sL = a.get(k,0)   if k<0 else 0
    def blocks_of(edges):                      # maximal runs of consecutive deposit edges
        bl=[]
        for p in edges:
            if bl and bl[-1][-1]==p-1: bl[-1].append(p)
            else: bl.append([p])
        return bl
    c=0
    # Each side = a sequence of blocks. EVERY gap costs (len - shield): the first gap
    # (spine -> nearest block) gets the boundary shield; every gap BETWEEN two blocks gets
    # shield 1 (the inner block's turn-around).
    R=blocks_of(sorted(p for p in nz if p>=spineR and f_of(p,k)==0))
    if R:
        c+=max(0,(R[0][0]-spineR)-shield_right(k,eps,dl,sR))
        for i in range(1,len(R)):
            c+=max(0,(R[i][0]-R[i-1][-1]-1)-1)
    L=blocks_of(sorted((p for p in nz if p+1<=spineL and f_of(p,k)==0),reverse=True))
    if L:
        c+=max(0,(spineL-L[0][0]-1)-shield_left(k,eps,dl,sL))
        for i in range(1,len(L)):
            c+=max(0,(L[i-1][-1]-L[i][0]-1)-1)
    return c+boundary_correction(eps,dl,k,a)

def boundary_correction(e,dl,k,a):
    # The sole residual corner of the block/gap model: k=0, dl=0 (both markers coincide at
    # site 0, end connecting left like start), an even deposit ADJACENT on the left (edge -1),
    # a right detour, and NO adjacent-right even deposit. The adjacent-left excursion donates
    # a turn that re-shields the right detour. Validated held-out to depth 23 (0 mismatch).
    if k!=0 or dl!=0: return 0
    a={j:v for j,v in a.items() if v}; nz=sorted(a)
    Lev=[p for p in nz if p<=-1]; Rev=[p for p in nz if p>=0]
    if not(Lev and Rev): return 0
    if max(Lev)!=-1: return 0          # need adjacent-left even (edge -1)
    if min(Rev)==0:  return 0          # adjacent-right even present -> not this corner
    return -1 if e==1 else (1 if a[-1]==2 else 0)

if __name__=="__main__":
    import sys,os,importlib.util
    import lamp_lib as LL
    HERE=os.path.dirname(os.path.abspath(__file__))
    def load(mod,path):
        sv=list(sys.argv);spec=importlib.util.spec_from_file_location(mod,os.path.join(HERE,path))
        m=importlib.util.module_from_spec(spec);sys.argv=[mod,'0'];spec.loader.exec_module(m);sys.argv=sv;return m
    cf=load('cf','catalytic_funceq.py'); rl=cf.relaxed_len_local
    D=int(sys.argv[1]) if len(sys.argv)>1 else 16
    dist=LL.bfs(D)
    miss=[]; n=0
    for (e,dl,k,L),d in dist.items():
        a=dict(L); r=rl(e,dl,k,a)
        if r is None: continue
        n+=1
        c_true=(d-r)//2; c_hat=c_pred(e,dl,k,a)
        if c_true!=c_hat: miss.append((c_true,c_hat,e,dl,k,a,r,d))
    print(f"depth {D}: {n} elts, {len(miss)} MISMATCHES (formula true={r}+2c)")
    miss.sort(key=lambda z:(abs(z[0]-z[1]),z[7]))
    for c_true,c_hat,e,dl,k,a,r,d in miss[:50]:
        print(f"  c_true={c_true} c_hat={c_hat} e={e:+d} dl={dl} k={k:+d} a={a} rel={r} true={d}")
