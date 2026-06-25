#!/usr/bin/env python3
# SEAM 2 (cross-field: modular forms / q-series mod p).  Compute the CLEAN bulk block
#   F(q,1) = sum_s F_s(q)   (q=x^2),  the partial-theta object underneath U, mod p, to
# high order, and probe it for structure the full U-assembly hides:
#   (a) p-kernel growth (is the clean block already maximally non-automatic?),
#   (b) eventual periodicity / Berlekamp-Massey linear complexity (rational floor),
#   (c) a PRODUCT form mod p:  does F(q,1) = prod (1-q^i)^{e_i} mod p for small e_i?
#       (an eta-quotient / modular form mod p would be a real structural handle),
#   (d) the theta-skeleton  F(q,1)*(q;q)_inf mod p  (clears the Euler denominator).
import sys
P = int(sys.argv[1]) if len(sys.argv)>1 else 3
M = int(sys.argv[2]) if len(sys.argv)>2 else 130     # q-order

# ---- F_s(q) via the section identity, mod P, to order M ----
def zeros(): return [0]*(M+1)
def shift(a,s):
    r=zeros()
    for i in range(M+1):
        if i+s<=M: r[i+s]=a[i]
    return r
F={s:zeros() for s in range(1,M+1)}
for _ in range(M+2):
    nf={}
    for s in range(1,M+1):
        t=zeros()
        if s<=M: t[s]=2%P
        S2=zeros()
        for sp in range(s,M+1):
            sh=shift(F[sp],sp)
            for i in range(M+1): S2[i]=(S2[i]+sh[i])%P
        t2=shift([(2*c)%P for c in S2],s)
        S3=zeros()
        for sp in range(1,s):
            for i in range(M+1): S3[i]=(S3[i]+F[sp][i])%P
        t3=shift([(2*c)%P for c in S3],2*s)
        nf[s]=[(t[i]+t2[i]+t3[i])%P for i in range(M+1)]
    F=nf
Fq1=zeros()
for s in range(1,M+1):
    for i in range(M+1): Fq1[i]=(Fq1[i]+F[s][i])%P    # F(q,1)=sum_s F_s, coeff in q
print(f"# F(q,1) mod {P}, coeffs [q^0..q^{min(M,40)}]:")
print("  "+" ".join(str(c) for c in Fq1[:41]))

# (a) p-kernel of the coefficient sequence
def kernel(seq,p,kmax=5,minov=4):
    N=len(seq)-1; elems=[]; growth=[]
    for k in range(kmax+1):
        pk=p**k;
        for r in range(pk):
            sub=tuple(seq[pk*n+r] for n in range((N-r)//pk+1) if pk*n+r<=N)
            if len(sub)<minov: continue
            if not any(len(e)>=minov and e[:min(len(e),len(sub))]==sub[:min(len(e),len(sub))] for e in elems):
                elems.append(sub)
        growth.append(len(elems))
    return growth
print(f"# (a) {P}-kernel growth of F(q,1) mod {P}: {kernel(Fq1,P)}  (full tree (p^k+..)= {[(P**(k+1)-1)//(P-1) for k in range(6)]})")

# (b) Berlekamp-Massey over F_P : linear complexity (rational <=> bounded)
def berlekamp_massey(s,p):
    C=[1]; B=[1]; L=0; m=1; b=1
    for n in range(len(s)):
        d=s[n]%p
        for i in range(1,L+1): d=(d+C[i]*s[n-i])%p
        if d==0: m+=1
        elif 2*L<=n:
            T=C[:]; coef=(d*pow(b,p-2,p))%p
            while len(C)<len(B)+m: C.append(0)
            for i in range(len(B)): C[i+m]=(C[i+m]-coef*B[i])%p
            L=n+1-L; B=T; b=d; m=1
        else:
            coef=(d*pow(b,p-2,p))%p
            while len(C)<len(B)+m: C.append(0)
            for i in range(len(B)): C[i+m]=(C[i+m]-coef*B[i])%p
            m+=1
    return L
lc=berlekamp_massey(Fq1,P)
print(f"# (b) linear complexity of F(q,1) mod {P} over {M+1} terms: {lc}  ({'~N/2 => NOT rational' if lc>M//3 else 'small => maybe rational'})")

# (c) product form:  log-derivative test.  If F=prod(1-q^i)^{e_i}, then
#     q F'/F = -sum_i e_i * i q^i/(1-q^i) = -sum_n (sum_{i|n} e_i i) q^n.  Solve for e_i mod P.
# Work with G=F/F[0] (need F[0] invertible). F(q,1)[0]=0 (starts at q^1), so test on 1+F or factor q.
G=[c for c in Fq1]
if G[0]%P==0:
    # F(q,1) = q*H(q) with H[0]!=0 ? check lowest term
    low=next((i for i,c in enumerate(G) if c%P),None)
    print(f"# (c) F(q,1) lowest term q^{low}; testing product form on H=F/q^{low}:")
    G=G[low:]
if G and G[0]%P:
    inv0=pow(G[0],P-2,P); G=[(inv0*c)%P for c in G]
    # qG'/G = L(q): compute logderiv series mod P
    Gp=[(i*G[i])%P for i in range(len(G))]              # qG'
    # divide Gp by G (series) mod P
    L=[0]*len(G)
    for n in range(len(G)):
        v=Gp[n]
        for k in range(1,n+1): v=(v-L[n-k]*G[k])%P
        L[n]=(v*pow(G[0],P-2,P))%P
    # L[n] = -sum_{i|n} e_i*i  => recover e_i by Mobius-like peeling
    e={}
    A=[(-L[n])%P for n in range(len(L))]                # A[n]=sum_{i|n} e_i*i
    for i in range(1,len(A)):
        s=0
        for j in range(2,len(A)//i+1):
            if (i*j)<len(A): pass
        ei=A[i]
        for d in range(1,i):
            if i%d==0: ei=(ei-((e.get(d) or 0)*d))%P   # p|d => e_d*d==0 mod p, so None->0 is exact
        # ei now = e_i * i ; divide by i mod P (if gcd(i,P)=1)
        if i%P: e[i]=(ei*pow(i%P,P-2,P))%P
        else:   e[i]=None       # exponent indeterminate mod P at multiples of P
    nonzero={i:v for i,v in e.items() if v not in (0,None)}
    print(f"# (c) eta/product exponents e_i mod {P} (i=1..30): "+
          " ".join(f'{i}:{e.get(i)}' for i in range(1,31)))
    print(f"#     #nonzero e_i in i<=120: {sum(1 for i in range(1,len(A)) if e.get(i) not in (0,None))}"
          f"  ({'BOUNDED => eta-quotient/modular!' if sum(1 for i in range(1,len(A)) if e.get(i) not in (0,None))<12 else 'GROWS => not a finite product mod p'})")
print("# done.")
