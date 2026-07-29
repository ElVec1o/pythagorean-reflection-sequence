# Count NEW merges per depth on the stratum alpha = pi/m, split by the type of
# the common element (translation vs not).  A merge is NEW when it is explained
# neither by equality in W_m = D_m * C_2 nor by equality at a generic shape.
from fractions import Fraction as Fr
import sys
from collections import defaultdict
MIN={3:[-1,1],4:[-2,0,1],5:[-1,-1,1],6:[-3,0,1],7:[1,-2,-1,1],
     9:[-1,-3,0,1],11:[-1,3,3,-4,-1,1]}      # monic minpoly of 2cos(pi/m)
def field(m):
    mp=[Fr(x) for x in MIN[m]]; DEG=len(mp)-1
    class NF:
        __slots__=("c",)
        def __init__(s,c): s.c=tuple(c)
        @classmethod
        def const(cls,v): return cls((Fr(v),)+(Fr(0),)*(DEG-1))
        @classmethod
        def gen(cls):
            return cls((Fr(0),Fr(1))+(Fr(0),)*(DEG-2)) if DEG>1 else cls((Fr(1),))
        def __add__(a,b): return NF(tuple(x+y for x,y in zip(a.c,b.c)))
        def __sub__(a,b): return NF(tuple(x-y for x,y in zip(a.c,b.c)))
        def __neg__(a): return NF(tuple(-x for x in a.c))
        def __eq__(a,b): return a.c==b.c
        def __hash__(a): return hash(a.c)
        def __mul__(a,b):
            f=[Fr(0)]*(2*DEG-1)
            for i,x in enumerate(a.c):
                if x:
                    for j,y in enumerate(b.c):
                        if y: f[i+j]+=x*y
            for k in range(2*DEG-2,DEG-1,-1):
                co=f[k]
                if co:
                    f[k]=Fr(0)
                    for i in range(DEG): f[k-DEG+i]-=co*mp[i]
            return NF(tuple(f[:DEG]))
        def inv(a):
            cols=[]; basis=NF.const(1); g=NF.gen()
            for i in range(DEG): cols.append((a*basis).c); basis=basis*g
            M=[[cols[c][r] for c in range(DEG)]+[Fr(1) if r==0 else Fr(0)] for r in range(DEG)]
            for col in range(DEG):
                piv=next(r for r in range(col,DEG) if M[r][col]!=0)
                M[col],M[piv]=M[piv],M[col]
                pv=M[col][col]; M[col]=[x/pv for x in M[col]]
                for r in range(DEG):
                    if r!=col and M[r][col]:
                        fq=M[r][col]; M[r]=[x-fq*y for x,y in zip(M[r],M[col])]
            return NF(tuple(M[r][DEG] for r in range(DEG)))
    class K:
        __slots__=("u","v"); S2=None
        def __init__(s,u,v): s.u=u; s.v=v
        @classmethod
        def const(cls,x): return cls(NF.const(x),NF.const(0))
        def __add__(a,b): return K(a.u+b.u,a.v+b.v)
        def __sub__(a,b): return K(a.u-b.u,a.v-b.v)
        def __neg__(a): return K(-a.u,-a.v)
        def __eq__(a,b): return a.u==b.u and a.v==b.v
        def __hash__(a): return hash((a.u,a.v))
        def __mul__(a,b): return K(a.u*b.u+a.v*b.v*K.S2, a.u*b.v+a.v*b.u)
        def inv(a):
            n=(a.u*a.u-a.v*a.v*K.S2).inv(); return K(a.u*n,-(a.v*n))
    C=NF.gen(); COSN=C*NF.const(Fr(1,2)); K.S2=NF.const(1)-COSN*COSN
    return NF,K,K(COSN,NF.const(0)),K(NF.const(0),NF.const(1))
def gens_strat(m,a,b):
    NF,K,COS,SIN=field(m)
    assert COS*COS+SIN*SIN==K.const(1)
    O=K.const(0); I=K.const(1)
    def refl(p0,d):
        L=d[0]*d[0]+d[1]*d[1]; Li=L.inv()
        m11=(d[0]*d[0]-d[1]*d[1])*Li; m12=(K.const(2)*d[0]*d[1])*Li
        return (m11,m12,m12,-m11,p0[0]-(m11*p0[0]+m12*p0[1]),p0[1]-(m12*p0[0]-m11*p0[1]))
    V0=(K.const(a),O); V1=(K.const(b)*COS,K.const(b)*SIN)
    G=[(I,O,O,-I,O,O),refl((O,O),(COS,SIN)),refl(V0,(V1[0]-V0[0],V1[1]-V0[1]))]
    ID=(I,O,O,I,O,O)
    for g in G:
        gg=(g[0]*g[0]+g[1]*g[2],g[0]*g[1]+g[1]*g[3],g[2]*g[0]+g[3]*g[2],
            g[2]*g[1]+g[3]*g[3],g[0]*g[4]+g[1]*g[5]+g[4],g[2]*g[4]+g[3]*g[5]+g[5])
        assert gg==ID
    return G,ID,K
def gens_gen():
    def refl(p0,p1):
        dx,dy=p1[0]-p0[0],p1[1]-p0[1]; L=dx*dx+dy*dy
        a=(dx*dx-dy*dy)/L; b=2*dx*dy/L
        return (a,b,b,-a,(1-a)*p0[0]-b*p0[1],-b*p0[0]+(1+a)*p0[1])
    V0=(Fr(0),Fr(0));V1=(Fr(1),Fr(0));V2=(Fr(1,3),Fr(1,2))
    return [refl(V0,V1),refl(V1,V2),refl(V2,V0)],(Fr(1),Fr(0),Fr(0),Fr(1),Fr(0),Fr(0))
def mul(g,h):
    return (g[0]*h[0]+g[1]*h[2],g[0]*h[1]+g[1]*h[3],g[2]*h[0]+g[3]*h[2],
            g[2]*h[1]+g[3]*h[3],g[0]*h[4]+g[1]*h[5]+g[4],g[2]*h[4]+g[3]*h[5]+g[5])
def wm_form(w,m):
    ID=(0,0); X={'0':(0,1),'1':((-1)%m,1)}; out=[]
    def mulD(g,h):
        j1,e1=g; j2,e2=h
        return ((j1+(j2 if e1==0 else -j2))%m,(e1+e2)%2)
    def push(sy):
        if sy[0]=='D' and sy[1]==ID: return
        if out and out[-1][0]=='C' and sy[0]=='C': out.pop(); return
        if out and out[-1][0]=='D' and sy[0]=='D':
            g=mulD(out.pop()[1],sy[1])
            if g!=ID: out.append(('D',g))
            return
        out.append(sy)
    for ch in w: push(('C',) if ch=='2' else ('D',X[ch]))
    return tuple(out)
def run(m,D,legs=(1,2)):
    GS,IDS,K=gens_strat(m,*legs); GG,IDG=gens_gen()
    front=[("",IDS,IDG)]
    res={}
    for d in range(1,D+1):
        nf=[]
        for (w,A,B) in front:
            last=int(w[-1]) if w else -1
            for i in range(3):
                if i!=last: nf.append((w+str(i),mul(A,GS[i]),mul(B,GG[i])))
        front=nf
        cls=defaultdict(list)
        for (w,A,B) in front: cls[A].append((w,B))
        tr=nt=0
        for A,items in cls.items():
            if len(items)<2: continue
            par={i:i for i in range(len(items))}
            def find(x):
                while par[x]!=x: par[x]=par[par[x]]; x=par[x]
                return x
            for i in range(len(items)):
                for j in range(i+1,len(items)):
                    if items[i][1]==items[j][1] or wm_form(items[i][0],m)==wm_form(items[j][0],m):
                        par[find(i)]=find(j)
            nparts=len({find(i) for i in range(len(items))})
            if nparts>1:
                istr = (A[0]==K.const(1) and A[1]==K.const(0)
                        and A[2]==K.const(0) and A[3]==K.const(1))
                if istr: tr+=nparts-1
                else: nt+=nparts-1
        res[d]=(tr,nt)
        print(f"  m={m} d={d:2d}: new merges  translation {tr:4d}   other {nt:4d}", flush=True)
    return res
D=int(sys.argv[2]) if len(sys.argv)>2 else 12
run(int(sys.argv[1]),D)
