# The cylindrical honeycomb X_m: Cayley graph of Phat_m = (Z/m x Z) x| C2.
# Same suffix-walk flow as the generic case, with the rho_1 exponent mod m.
# Verifies: V(flow) = translation part; faces = wrapped sites; the wrapping
# cycle gamma (flow of (x_0x_1)^m) has V(gamma) = 0; and the m=5 depth-12
# translation relations are exactly pairs whose flows differ by a wrapping cycle.
exec(open("cylinder_structure.py").read().split("D=12")[0])
from collections import Counter
M=5
GS,IDEL=gens_strat(1,2)          # exact in Q(2cos pi/5)(sin pi/5)
S=[ (g[0],g[1],g[2],g[3]) for g in GS ]
TV=[ (g[4],g[5]) for g in GS ]
def matvec(A,v): return (A[0]*v[0]+A[1]*v[1], A[2]*v[0]+A[3]*v[1])
def matmul(A,B): return (A[0]*B[0]+A[1]*B[2], A[0]*B[1]+A[1]*B[3],
                         A[2]*B[0]+A[3]*B[2], A[2]*B[1]+A[3]*B[3])
ID2=(K.const(1),K.const(0),K.const(0),K.const(1))
for i in range(3):
    assert matvec(S[i],TV[i])==tuple(-x for x in TV[i]), "S_i v_i != -v_i"
def stepv(v,i,m=M):
    a,b,e=v
    if i==0: return (a,b,1-e)
    if i==1: return ((a-1)%m,b,1) if e==0 else ((a+1)%m,b,0)
    return (a,b-1,1) if e==0 else (a,b+1,0)
E0=(0,0,0)
def edge_of(u,i):
    w=stepv(u,i)
    return (u,w,i) if u[2]==0 else (w,u,i)
_dep={}
def word_flow(word):
    fl=Counter(); tot=(K.const(0),K.const(0)); nf=E0; mat=ID2
    for ch in word:
        i=int(ch)
        dep=matvec(mat,TV[i])
        tot=(tot[0]+dep[0],tot[1]+dep[1])
        e=edge_of(nf,i); sgn=1 if nf[2]==0 else -1
        cd=dep if sgn==1 else tuple(-x for x in dep)
        old=_dep.setdefault(e,cd)
        assert old==cd, "edge deposit not direction-consistent on the cylinder"
        fl[e]+=sgn
        nf=stepv(nf,i); mat=matmul(mat,S[i])
    return Counter({e:c for e,c in fl.items() if c}), tot, nf, mat
def V(fl):
    x=K.const(0); y=K.const(0)
    for e,c in fl.items():
        d=_dep[e]
        for _ in range(abs(c)):
            if c>0: x=x+d[0]; y=y+d[1]
            else:   x=x-d[0]; y=y-d[1]
    return (x,y)
# faces = wrapped sites
T1="012012"
def conj(n,j):
    c=("01"*n if n>=0 else "10"*(-n)) + ("02"*j if j>=0 else "20"*(-j))
    return c+T1+c[::-1]
FACE={}; VEC={}
for n in range(-6,7):
    for j in range(-6,7):
        fl,tot,nf,mat=word_flow(conj(n,j))
        assert nf==E0 and mat==ID2
        assert V(fl)==tot
        assert len(fl)==6 and all(abs(c)==1 for c in fl.values()), f"face ({n},{j}) not a hexagon"
        FACE[(n%M,j)]=dict(fl) if (n%M,j) not in FACE else FACE[(n%M,j)]
        VEC.setdefault((n%M,j),tot)
        if (n%M,j) in VEC: assert VEC[(n%M,j)]==tot, f"wrapped sites disagree at ({n},{j})"
print(f"faces on the cylinder: {len(FACE)} distinct wrapped sites; "
      f"t_(n,j) = t_(n+{M},j) verified on the window")
# the wrapping cycle
gfl,gtot,gnf,gmat=word_flow("01"*M)
print(f"wrapping cycle gamma: |support| = {len(gfl)}, closed = {gnf==E0 and gmat==ID2}, "
      f"V(gamma) = 0 ? {gtot==(K.const(0),K.const(0))} and V(flow)=0 ? {V(gfl)==(K.const(0),K.const(0))}")
# the three translation-type m=5 relations found at depth 12
pairs=[("101010201210","210201201012"),
       ("102010101210","210210102102"),
       ("102012101010","201012012102")]
def shift(fl,dj):
    return Counter({((u[0],u[1]+dj,u[2]),(v[0],v[1]+dj,v[2]),i):c for (u,v,i),c in fl.items()})
for w1,w2 in pairs:
    f1,t1,n1,m1_=word_flow(w1); f2,t2,n2,m2_=word_flow(w2)
    assert t1==t2, "not the same element"
    d=Counter(f1); 
    for e,c in f2.items(): d[e]-=c
    d=Counter({e:c for e,c in d.items() if c})
    match=None
    for dj in range(-4,5):
        for k in (1,-1):
            g=shift(gfl,dj)
            if all(d.get(e,0)==k*c for e,c in g.items()) and len(d)==len(g):
                match=(dj,k)
    print(f"  {w1} = {w2}: flow difference has {len(d)} edges; "
          f"equals {'gamma shifted by j=%d, sign %+d' % match if match else 'NOT a single wrapping cycle'}")
