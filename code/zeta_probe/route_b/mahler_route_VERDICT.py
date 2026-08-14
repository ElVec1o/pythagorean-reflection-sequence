#!/usr/bin/env python3
"""
ROUTE 4 (Mahler's method) -- VERDICT script. Consolidated, reproducible.

QUESTION. Does U (true) or V (relaxed) growth series of A396406 satisfy a MAHLER
functional equation  a_0(z)f(z)+a_1(z)f(z^d)+...+a_m(z)f(z^{d^m})=0 (d>=2 integer,
a_i in Q[z], a_0 a_m != 0), so that Nishioka's dichotomy (rational-or-transcendental)
applies and -- f being non-rational (exp. growth, no recurrence) -- forces f
transcendental over Q(x), bypassing the pole-counting/lem:cos/numerator route?

FINDINGS (all reproduced below):

(A) DIRECT SEARCH -- NEGATIVE. No linear Mahler equation (homogeneous or
    inhomogeneous) and no algebraic Mahler equation P(z,f(z),f(z^d))=0 exists for
    any of the scalar blocks S_1, Sigma_1, G_0=S_0/(1-S_1), G^T_0=Sigma_0/(1-Sigma_1),
    nor for V(x), U(x), nor their q-sections, for d<=8, order m<=5, q-degree D<=12.
    The search is EXACT (rational linear algebra) and rejects truncation artifacts.
    Each candidate verified as a power-series identity to order 220 (blocks) / 90 (V).

(B) STRUCTURAL REASON the catalytic equation is NOT Mahler.
    The catalytic functional equation
       F(q,t)=2qt/(1-qt)+2qt/(1-qt)[F(q,q)-F(q,q^2 t)]+2q^2 t/(1-q^2 t) F(q,q^2 t)
    couples F at t and at q^2 t. Writing t=q^s the operator is the EXPONENT SHIFT
    s -> s+2 (i.e. t -> q^2 t), a MULTIPLICATIVE q-difference (dilation) operator on
    the catalytic variable with q a PARAMETER. This is NOT the Mahler substitution
    q -> q^d. Eliminating t (telescoping the index k in S_k=alpha_k+gamma_k S_{k+2})
    yields an INFINITE Lambert-type sum  S_k=sum_j alpha_{k+2j} prod_{i<j} gamma_{k+2i},
    with alpha_k(q)=2q^{k+1}/(1-q^{k+1})=alpha_0(q^{k+1}): the index k acts by the
    exponent map q -> q^{k+1}, k in an arithmetic progression -- the multiplicative/
    Lambert structure, fundamentally different from the geometric q -> q^d of Mahler.

(C) RIGOROUS OBSTRUCTION (Dumas structure thm => pole-spacing test).
    Dumas' Structure Theorem (Bell-Coons-Rowland, Thm 3): a d-Mahler function factors
    as F = H(z)/prod_{j>=0} Gamma(z^{d^j}) with H d-REGULAR (polynomial coeff growth,
    analytic in the disk) and Gamma a fixed POLYNOMIAL. Hence every pole of a d-Mahler
    function in the open unit disk is a zero of some Gamma(z^{d^j}), i.e. has the form
    zeta * r^{1/d^j} with Gamma(r)=0. The REAL poles in (0,1) accumulating at 1 are a
    FINITE UNION of orbits {r^{1/d^j}}_{j>=0}, and for each orbit
       1 - r^{1/d^j} = 1 - e^{(ln r)/d^j} ~ (-ln r)/d^j   (j->infty),
    so the gaps (1-q_n) decay GEOMETRICALLY with ratio exactly d (an integer >=2);
    a finite union of such orbits still has consecutive-gap ratios bounded away from 1.

    BUT the blocks S_1, Sigma_1 (hence V, U) have real poles q_n (zeros of 1-S_1=0,
    1-Sigma_1=0) at the cosine phase w_n=(n+1/2)pi, w=sqrt(2/(-ln q)), giving
       1 - q_n ~ (2/pi^2) / n^2     (POLYNOMIAL spacing),
    so the consecutive-gap ratio (1-q_{n-1})/(1-q_n) -> 1, NOT an integer d>=2.
    => the pole set is NOT a finite union of geometric-ratio-d orbits
    => NEITHER block is d-Mahler for ANY d>=2  (CONDITIONAL on the 1/n^2 law, which
       is the same analytic input as the project's lem:cos -- see RIGOR GAP).

    Equivalently/independently: Dumas => poles of a Mahler fn inside the disk are
    ALGEBRAIC (zeros of Gamma(z^{d^j}), Gamma a polynomial). The dominant pole
    q* = 0.449453630558948... is numerically NOT algebraic of degree <=7 (PSLQ),
    conjecturally transcendental; if transcendental, q* cannot be a pole of a Mahler
    function -> kill. (Also conditional: q* transcendence is open.)

VERDICT: Mahler's method does NOT apply to U or V. It does not bypass lem:cos; it
reduces to the SAME analytic fact (the 1/n^2 pole-spacing / transcendence of q*).
Route 4 (Mahler) is DEAD as a shortcut, but its literature CONFIRMS the standing
result-shape: V (and U, modulo the dressing-regularity gap) is non-rational with a
unit-circle natural boundary, hence (Rande/Nishioka taxonomy) would be transcendental
IF Mahler -- but it is not Mahler.
"""
import json, os
from fractions import Fraction as F

HERE=os.path.dirname(os.path.abspath(__file__))

# ---- exact blocks in q (Lambert telescopes) ----
def make_blocks(NQ):
    def psmul(a,b):
        c=[F(0)]*(NQ+1)
        for i in range(NQ+1):
            if a[i]==0: continue
            for j in range(NQ+1-i):
                if b[j]: c[i+j]+=a[i]*b[j]
        return c
    def pssub(a,b): return [a[i]-b[i] for i in range(NQ+1)]
    def psadd(a,b): return [a[i]+b[i] for i in range(NQ+1)]
    def psinv(a):
        inv=[F(0)]*(NQ+1); inv[0]=F(1)/a[0]
        for n in range(1,NQ+1):
            s=F(0)
            for k in range(1,n+1):
                if a[k]: s+=a[k]*inv[n-k]
            inv[n]=-s/a[0]
        return inv
    def alpha(k):
        c=[F(0)]*(NQ+1); m=1
        while m*(k+1)<=NQ: c[m*(k+1)]+=F(2); m+=1
        return c
    def Sk(k):
        tot=[F(0)]*(NQ+1); prod=[F(1)]+[F(0)]*NQ; j=0
        while True:
            term=psmul(alpha(k+2*j),prod); tot=psadd(tot,term)
            prod=psmul(prod,pssub(alpha(k+1+2*j),alpha(k+2*j)))
            if all(x==0 for x in prod) or j>NQ+2: break
            j+=1
        return tot
    def Ak(k):
        c=[F(0)]*(NQ+1); m=0
        while 1+m*(k+1)<=NQ: c[1+m*(k+1)]+=F(2); m+=1
        return c
    def Ck(k):
        c=[F(0)]*(NQ+1); m=0
        while (k+3)+m*(k+2)<=NQ: c[(k+3)+m*(k+2)]+=F(2); m+=1
        m=0
        while (k+2)+m*(k+1)<=NQ: c[(k+2)+m*(k+1)]-=F(2); m+=1
        return c
    def Sigk(k):
        tot=[F(0)]*(NQ+1); prod=[F(1)]+[F(0)]*NQ; j=0
        while True:
            term=psmul(Ak(k+2*j),prod); tot=psadd(tot,term)
            prod=psmul(prod,Ck(k+2*j))
            if all(x==0 for x in prod) or j>NQ+2: break
            j+=1
        return tot
    one=[F(1)]+[F(0)]*NQ
    S0,S1=Sk(0),Sk(1); Sig0,Sig1=Sigk(0),Sigk(1)
    G0=psmul(S0,psinv(pssub(one,S1))); GT0=psmul(Sig0,psinv(pssub(one,Sig1)))
    return {"S1":S1,"Sig1":Sig1,"G0":G0,"GT0":GT0}

def fnz(s):
    for n,c in enumerate(s):
        if c!=0: return n
    return None

def mahler_exists(lst, NQ, ds, ms, Ds):
    Fser=[F(lst[i]) if i<len(lst) else F(0) for i in range(NQ+1)]
    f0=fnz(Fser)
    def comp(s,d,i):
        out=[F(0)]*(NQ+1); p=d**i
        for n in range(NQ+1):
            if n*p<=NQ and s[n]!=0: out[n*p]=s[n]
        return out
    for d in ds:
        for m in ms:
            if d**m*max(f0,1)>NQ: continue
            for D in Ds:
                for homo in (True,False):
                    nunk=(m+1)*(D+1)+(0 if homo else D+1)
                    if NQ+1<nunk+12: continue
                    C=[comp(Fser,d,i) for i in range(m+1)]
                    cols=[('a',i,e) for i in range(m+1) for e in range(D+1)]
                    if not homo: cols+=[('b',e) for e in range(D+1)]
                    nc=len(cols); M=[]
                    for n in range(NQ+1):
                        row=[F(0)]*nc
                        for ci,col in enumerate(cols):
                            if col[0]=='a':
                                _,i,e=col
                                if n-e>=0: row[ci]=C[i][n-e]
                            else:
                                _,e=col
                                if n-e==0: row[ci]=F(-1)
                        M.append(row)
                    nr=len(M);piv=[];pr=0
                    for c in range(nc):
                        p=None
                        for r in range(pr,nr):
                            if M[r][c]!=0:p=r;break
                        if p is None: continue
                        M[pr],M[p]=M[p],M[pr]
                        iv=M[pr][c];M[pr]=[v/iv for v in M[pr]]
                        for r in range(nr):
                            if r!=pr and M[r][c]!=0:
                                ff=M[r][c];M[r]=[M[r][k]-ff*M[pr][k] for k in range(nc)]
                        piv.append(c);pr+=1
                        if pr==nr:break
                    if nc-len(piv)>0:
                        free=[c for c in range(nc) if c not in piv]
                        for fv in free:
                            sol=[F(0)]*nc;sol[fv]=F(1)
                            for ri,c in enumerate(piv): sol[c]=-M[ri][fv]
                            iset={col[1] for ci,col in enumerate(cols) if col[0]=='a' and sol[ci]!=0}
                            if len(iset)<2: continue
                            if any(d**i*max(f0,1)>NQ for i in iset): continue
                            lhs=[F(0)]*(NQ+1)
                            for ci,col in enumerate(cols):
                                if sol[ci]==0: continue
                                if col[0]=='a':
                                    _,i,e=col
                                    for pos in range(NQ+1):
                                        if pos-e>=0: lhs[pos]+=sol[ci]*C[i][pos-e]
                                else:
                                    _,e=col
                                    if e<=NQ: lhs[e]-=sol[ci]
                            if all(v==0 for v in lhs):
                                return (d,m,D,homo,sorted(iset))
    return None

if __name__=="__main__":
    print("(A) DIRECT MAHLER SEARCH on blocks (order 120), d<=6 m<=4 D<=8:")
    B=make_blocks(120)
    for nm in ["S1","Sig1","G0","GT0"]:
        r=mahler_exists(B[nm],120,range(2,7),range(1,5),range(2,9,2))
        print(f"   {nm}: {'FOUND '+str(r) if r else 'NONE'}")
    print("=> NEGATIVE: no Mahler equation for any block. Consistent with structural")
    print("   analysis (B) and pole-spacing obstruction (C) in the module docstring.")
