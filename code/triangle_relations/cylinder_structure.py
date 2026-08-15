# The cylindrical honeycomb X_m: Cayley graph of Phat_m = (Z/m x Z) x| C2.
# Same suffix-walk flow as the generic case, with the rho_1 exponent mod m.
# Verifies: V(flow) = translation part; faces = wrapped sites; the wrapping
# cycle gamma (flow of (x_0x_1)^m) has V(gamma) = 0; and the m=5 depth-12
# translation relations are exactly pairs whose flows differ by a wrapping cycle.
# Pulls in the exact-arithmetic layer of stratum_fields.py (the number field, the
# stratum generators) while cutting off that file's own command-line driver.
exec(open("stratum_fields.py").read().split("D=int(sys.argv")[0])
from collections import Counter
M=5
GS,IDEL,K=gens_strat(M,1,2)      # exact in Q(2cos pi/5)(sin pi/5)
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

# ---------------------------------------------------------------------------
# Theorem "Stratum metric" (ii), the clause carrying the range 2 <= m <= 12:
#     gamma_j - gamma_{j-1}  =  sum of the m faces of level j.
# Both sides are finitely supported 1-flows on X_m = Cay((Z/m x Z) x| C2), so
# the identity is combinatorial: it never touches the number field, and the
# exact-arithmetic layer above (which carries minimal polynomials for
# m in {3,4,5,6,7,9,11} only) is not needed and would not cover the range.
# gamma_j is computed as the flow of the CONJUGATED word, not by translating
# gamma_0, so the check does not presuppose that conjugation acts as a shift.
def flow_comb(word,m):
    """Suffix-walk flow of a word on X_m, as a signed edge counter."""
    fl=Counter(); nf=(0,0,0)
    for ch in word:
        i=int(ch); w=stepv(nf,i,m)
        e=(nf,w,i) if nf[2]==0 else (w,nf,i)
        fl[e]+= 1 if nf[2]==0 else -1
        nf=w
    return Counter({e:c for e,c in fl.items() if c}), nf
def conj_word(pre,core):
    return pre+core+pre[::-1]
def rot(j):   return ("02"*j) if j>=0 else ("20"*(-j))
def apex(n):  return ("01"*n) if n>=0 else ("10"*(-n))
print("level identity gamma_j - gamma_(j-1) = sum of the m faces of level j:")
for m in range(2,13):
    gam={}
    for j in range(-3,4):
        g,end=flow_comb(conj_word(rot(j),"01"*m),m)
        assert end==(0,0,0), f"m={m}: wrapping cycle not closed"
        gam[j]=g
    okj=[]
    for j in (-1,0,1):
        L=Counter()
        for n in range(m):
            f,endf=flow_comb(conj_word(rot(j)+apex(n),"012012"),m)
            assert endf==(0,0,0), f"m={m}: face ({n},{j}) not closed"
            assert len(f)==6 and all(abs(c)==1 for c in f.values()), \
                f"m={m}: face ({n},{j}) is not a hexagon"
            for e,c in f.items(): L[e]+=c
        L=Counter({e:c for e,c in L.items() if c})
        D=Counter(gam[j])
        for e,c in gam[j-1].items(): D[e]-=c
        D=Counter({e:c for e,c in D.items() if c})
        okj.append(L==D)
    print(f"  m={m:2d}: |gamma| = {len(gam[0]):3d}, level sum = {len(L):3d} edges, "
          f"identity at j=-1,0,+1: {'OK' if all(okj) else 'FAILS ' + str(okj)}")
    assert all(okj), f"m={m}: level identity fails"
print("  identity holds for every m in 2..12 (this is the range the theorem states)")
