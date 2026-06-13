# Guess an algebraic equation P(x, F(x)) = 0 for F = sum u_n x^n, exact over Q.
from fractions import Fraction as F
u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,
17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,
2554961,3848384,5777651,8679441,13031206,19574659,29338781,
43997388,65932461,98849591,147969934]
N=len(u)  # 43 series coeffs, orders 0..42
fser=[F(x) for x in u]
def mul(a,b):
    r=[F(0)]*N
    for i in range(N):
        if a[i]==0: continue
        for j in range(N-i):
            if b[j]==0: continue
            r[i+j]+=a[i]*b[j]
    return r
# powers of F: F^0..F^dymax
def powers(dymax):
    P=[[F(0)]*N for _ in range(dymax+1)]
    P[0][0]=F(1)
    for j in range(1,dymax+1):
        P[j]=mul(P[j-1],fser)
    return P
def nullspace(rows):
    M=[r[:] for r in rows]; nr=len(M); nc=len(M[0]); piv=[]; r=0
    for c in range(nc):
        p=None
        for i in range(r,nr):
            if M[i][c]!=0: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        piv.append(c); r+=1
    free=[c for c in range(nc) if c not in piv]
    sols=[]
    for fc in free:
        v=[F(0)]*nc; v[fc]=F(1)
        for ri,pc in enumerate(piv): v[pc]=-M[ri][fc]
        sols.append(v)
    return sols
def trial(dx,dy):
    # unknowns c_{i,j}, i in 0..dx, j in 0..dy ; P(x,F)=sum c_{ij} x^i F^j
    P=powers(dy)
    cols=[]  # each col is the series x^i * F^j, as length-N coeff vector
    idx=[]
    for j in range(dy+1):
        for i in range(dx+1):
            col=[F(0)]*N
            for n in range(N):
                if n-i>=0: col[n]=P[j][n-i]
            cols.append(col); idx.append((i,j))
    nunk=len(cols)
    # rows = orders 0..N-1 ; matrix[row][col]
    rows=[[cols[c][n] for c in range(nunk)] for n in range(N)]
    ns=nullspace(rows)
    # require: a null vector with a nonzero coeff on some j>=2 (genuinely nonlinear),
    # and over-determination margin = N - nunk > 6
    margin=N-nunk
    real=[]
    for v in ns:
        if any(v[c]!=0 for c in range(nunk) if idx[c][1]>=2):
            real.append(v)
    return nunk,margin,real,idx
print("dx dy unknowns margin  -> nonlinear-algebraic null vectors")
best=None
for dy in range(2,5):
    for dx in range(2,12):
        nunk,margin,real,idx=trial(dx,dy)
        if margin<5: continue
        tag = f"FOUND ({len(real)})" if real else "none"
        if real and best is None: best=(dx,dy,real[0],idx,margin)
        if real or (dx<=6):
            print(f"{dx:2d} {dy:2d}  {nunk:3d}     {margin:3d}    {tag}")
if best:
    dx,dy,v,idx,margin=best
    print(f"\nMINIMAL ALGEBRAIC EQUATION  dx={dx} dy={dy}, over-determined by {margin}:")
    # print P(x,y) = sum c_ij x^i y^j  ; clear denominators
    from math import gcd
    dens=[c.denominator for c in v if c!=0]
    import functools
    L=functools.reduce(lambda a,b: a*b//gcd(a,b), dens,1)
    ic=[int(c*L) for c in v]
    g=functools.reduce(gcd,[abs(x) for x in ic if x!=0])
    ic=[x//g for x in ic]
    terms={}
    for c,(i,j) in zip(ic,idx):
        if c!=0: terms[(i,j)]=c
    for j in range(dy+1):
        row=[f"{terms[(i,j)]}*x^{i}" for i in range(dx+1) if (i,j) in terms]
        if row: print(f"  y^{j}: " + " + ".join(row))
else:
    print("\nNO algebraic equation of degree<=4 in F with these x-degrees fits 43 terms.")
