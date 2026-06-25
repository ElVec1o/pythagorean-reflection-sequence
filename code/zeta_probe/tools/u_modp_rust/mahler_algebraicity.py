#!/usr/bin/env python3
# SEAM 1: the definitive algebraicity test for U mod p, in Mahler-base-p form.
# In F_p[[x]], Frobenius gives U^{p^i}=U(x^{p^i}); U is algebraic over F_p(x) IFF the
# Frobenius powers are F_p(x)-dependent, i.e. there exist A_i in F_p[x] (deg<=D), not
# all 0, with  sum_{i=0}^{n} A_i(x) U(x^{p^i}) = 0 mod p.  (base p = char p => Mahler<=>algebraic.)
# We search for such a relation by nullspace over F_p of the coefficient matrix.
# NO relation up to (n,D) with #equations >> #unknowns  =>  U mod p is not algebraic of
# Frobenius-depth<=n and height<=D  =>  transcendence evidence, with explicit bounds.
import sys
P = int(sys.argv[2]) if len(sys.argv)>2 else 3
u = [int(t) for t in open(sys.argv[1]).read().split()]   # u_0..u_N mod P
N = len(u)-1
print(f"# U mod {P}, have u_0..u_{N}  ({N+1} terms)")

def Ui_coeff(i, m):           # [x^m] U(x^{p^i}) = u_{m/p^i} if p^i | m and quotient<=N
    pi = P**i
    if m % pi: return 0
    q = m//pi
    return u[q] if q<=N else None      # None = unknown (beyond data)

def rref_nullity(rows, ncols):
    # Gaussian elimination over F_P; return (rank, nullity, one nullvector or None)
    R=[r[:] for r in rows]; piv=[]; r=0
    for c in range(ncols):
        pr=None
        for rr in range(r,len(R)):
            if R[rr][c]%P: pr=rr; break
        if pr is None: continue
        R[r],R[pr]=R[pr],R[r]
        inv=pow(R[r][c],P-2,P)
        R[r]=[(inv*v)%P for v in R[r]]
        for rr in range(len(R)):
            if rr!=r and R[rr][c]%P:
                f=R[rr][c]; R[rr]=[(R[rr][k]-f*R[r][k])%P for k in range(ncols)]
        piv.append(c); r+=1
        if r==len(R): break
    rank=len(piv); nullity=ncols-rank
    nv=None
    if nullity>0:
        free=[c for c in range(ncols) if c not in piv]
        fc=free[0]; nv=[0]*ncols; nv[fc]=1
        for idx,c in enumerate(piv):
            nv[c]=(-R[idx][fc])%P
    return rank,nullity,nv

print(f"# {'depth n':>8} {'deg D':>6} {'unknowns':>9} {'eqs':>5} {'nullity':>8}  verdict")
for n in range(1,5):
    for D in [8,16,24,32,44]:
        ncols=(n+1)*(D+1)
        # use exponents e where ALL needed U_i[e-d] are known (q<=N); cap eqs so matrix is valid
        rows=[]; e=0; Mmax=N           # U_0=U(x) only known to x^N, so e<=N
        for e in range(0, Mmax+1):
            row=[0]*ncols; ok=True
            for i in range(n+1):
                for d in range(D+1):
                    col=i*(D+1)+d
                    if e-d<0: continue
                    cval=Ui_coeff(i,e-d)
                    if cval is None: ok=False; break
                    row[col]=(row[col]+cval)%P
                if not ok: break
            if ok: rows.append(row)
        eqs=len(rows)
        if eqs <= ncols+5:            # not enough equations to be conclusive
            print(f"  {n:>8} {D:>6} {ncols:>9} {eqs:>5} {'--':>8}  (underdetermined, skip)")
            continue
        rank,nullity,nv=rref_nullity(rows,ncols)
        if nullity==0:
            verdict=f"NO relation  => not algebraic of depth<={n}, height<={D}"
        else:
            verdict=f"*** RELATION FOUND (nullity {nullity}) -- CHECK (algebraic?!)"
        print(f"  {n:>8} {D:>6} {ncols:>9} {eqs:>5} {nullity:>8}  {verdict}")
print("# (depth n = Frobenius levels U(x),U(x^p),...,U(x^{p^n}); height D = max deg A_i.)")
