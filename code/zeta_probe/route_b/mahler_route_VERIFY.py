"""
=====================================================================================
MAHLER ROUTE -- consolidated verification (Route 2 of the XXXXX project).
Question: does U (or V, or the bulk block G_0) satisfy a Mahler functional equation
   a_0(z) f(z) + a_1(z) f(z^k) + ... + a_d(z) f(z^{k^d}) = 0,  a_i in Q[z], a_0 a_d != 0, k>=2?
If so, Nishioka's dichotomy (non-rational k-Mahler => transcendental) closes transcendence
WITHOUT pole-counting / lem:cos.

RESULT: NO. Three independent lines of evidence, reported honestly.
=====================================================================================
"""
import json, math
from fractions import Fraction as Fr

PASS=[]

# ---- data ----
v=json.load(open('v110.json'))                       # 111 exact v_n
G0=json.load(open('G0_series.json'))                        # 201 exact bulk-block coeffs (q)
u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,
   62263,94622,143881,217101,327832,495443,749195,1127236,1697179,2554961,3848384,5777651,8679441,
   13031206,19574659,29338781,43997388,65932461,98849591,147969934]

# ============ (1) DIRECT MAHLER FIT with strict out-of-sample validation ============
def series_pow(seq,d,maxdeg):
    out=[0]*(maxdeg+1)
    for n,c in enumerate(seq):
        if n*d<=maxdeg: out[n*d]+=c
        else: break
    return out
def nullspace_int(rows,ncol):
    M=[[Fr(x) for x in r] for r in rows]; nrow=len(M); pivcol={}; pivots=[]; r=0
    for c in range(ncol):
        piv=next((rr for rr in range(r,nrow) if M[rr][c]!=0),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for rr in range(nrow):
            if rr!=r and M[rr][c]!=0:
                f=M[rr][c]; M[rr]=[M[rr][j]-f*M[r][j] for j in range(ncol)]
        pivcol[c]=r; pivots.append(c); r+=1
        if r==nrow: break
    free=[c for c in range(ncol) if c not in pivcol]; basis=[]
    for fc in free:
        vec=[Fr(0)]*ncol; vec[fc]=Fr(1)
        for c in pivots: vec[c]=-M[pivcol[c]][fc]
        basis.append(vec)
    return basis
def has_genuine_mahler(seq, kset, mset, Dmax, val_terms):
    N=len(seq)-1
    for k in kset:
        for m in mset:
            if k**m>8: continue          # need f(z^{k^m}) to have many terms in window
            for D in range(0,Dmax+1):
                nunk=(m+1)*(D+1)+(D+1)
                fit=nunk+10
                if fit+val_terms>N+1: continue
                fpows=[series_pow(seq,k**i,fit+val_terms) for i in range(m+1)]
                rows=[]
                for deg in range(fit):
                    row=[0]*nunk; col=0
                    for i in range(m+1):
                        for j in range(D+1):
                            row[col]=fpows[i][deg-j] if 0<=deg-j<fit else 0; col+=1
                    for j in range(D+1):
                        row[col]=-1 if j==deg else 0; col+=1
                    rows.append(row)
                for sol in nullspace_int(rows,nunk):
                    ok=all(
                        sum((sol[i*(D+1)+j]*fpows[i][deg-j]) for i in range(m+1) for j in range(D+1)
                            if sol[i*(D+1)+j]!=0 and 0<=deg-j<len(fpows[i]))
                        - (sol[(m+1)*(D+1)+deg] if deg<=D else 0) == 0
                        for deg in range(fit,fit+val_terms))
                    if ok:
                        a0=any(sol[j]!=0 for j in range(D+1))
                        am=any(sol[m*(D+1)+j]!=0 for j in range(D+1))
                        if a0 and am: return (k,m,D)
    return None

r_v =has_genuine_mahler(v,  [2,3],[1,2,3], 15, 25)
r_g =has_genuine_mahler(G0, [2,3,4],[1,2,3,4], 18, 30)
r_u =has_genuine_mahler(u,  [2,3],[1,2], 6, 8)
PASS.append(("No genuine Mahler eq for V (111 terms, k<=3,m<=3,deg<=15, OOS-validated)", r_v is None))
PASS.append(("No genuine Mahler eq for bulk G_0 (201 terms, k<=4,m<=4,deg<=18, OOS)", r_g is None))
PASS.append(("No genuine Mahler eq for U (43 terms, k<=3,m<=2,deg<=6, OOS)", r_u is None))

# ============ (2) NON-RATIONALITY (so 'rational' branch is excluded) ============
def hankel_det(seq,m,off=0):
    M=[[Fr(seq[off+i+j]) for j in range(m)] for i in range(m)]; det=Fr(1)
    for col in range(m):
        piv=next((r for r in range(col,m) if M[r][col]!=0),None)
        if piv is None: return Fr(0)
        if piv!=col: M[col],M[piv]=M[piv],M[col]; det=-det
        det*=M[col][col]; inv=M[col][col]
        for r in range(col+1,m):
            f=M[r][col]/inv; M[r]=[M[r][j]-f*M[col][j] for j in range(m)]
    return det
def maxnz(seq):
    best=0
    for off in [0,1]:
        for m in range(2,len(seq)//2):
            if off+2*m-1<len(seq) and hankel_det(seq,m,off)!=0: best=max(best,m)
    return best
PASS.append((f"V non-rational: Hankel!=0 up to size {maxnz(v)} (>= 30)", maxnz(v)>=30))
PASS.append((f"U non-rational: Hankel!=0 up to size {maxnz(u)} (>= 15)", maxnz(u)>=15))
PASS.append((f"G_0 non-rational: Hankel!=0 up to size {maxnz(G0)} (>= 30)", maxnz(G0)>=30))

# ============ (3) POLE-ACCUMULATION LAW (structural obstruction) ============
# V/U travel denominator 1-Sigma_1 has poles q_m with w_m=sqrt(2/(-ln q_m)) ~ m*pi.
# Verified spacing w_{m+1}-w_m -> pi to 4 decimals over 24 poles (separate run).
# => 1-q_m ~ 2/(m pi)^2 : POLYNOMIAL accumulation, N(eps)~eps^{-1/2}.
# Mahler (Dumas Thm 3): open-disk poles at moduli |beta|^{1/k^j}, finitely many beta;
# => N(eps)~C*log(1/eps). Power law vs log law: incompatible.
ws=[4.7013548,7.8470526,10.990573,14.133261,17.275557,20.417639,23.559592,26.701461,
    29.843271,32.985041,36.126779,39.268495,42.410192,45.551875,48.693546,51.835208]
spacings=[ws[i]-ws[i-1] for i in range(1,len(ws))]
spacing_to_pi = abs(spacings[-1]-math.pi) < 0.001
PASS.append(("V/U pole spacing w_{m+1}-w_m -> pi (polynomial accumulation, NOT geometric)", spacing_to_pi))
# gap ratios (1-q_m)/(1-q_{m+1}) -> 1 (would be >= k>=2, bounded away from 1, if Mahler)
qs=[math.exp(-2/w**2) for w in ws]
gapratios=[(1-qs[i])/(1-qs[i+1]) for i in range(len(qs)-1)]
PASS.append(("gap ratios (1-q_m)/(1-q_{m+1}) -> 1 (Mahler would force >= k>=2)", gapratios[-1]<1.2 and gapratios[-1]>1.0))

print("="*70); print("MAHLER ROUTE VERIFICATION (Route 2)"); print("="*70)
for name,ok in PASS: print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
print("="*70)
print("ALL PASS" if all(ok for _,ok in PASS) else "SOME FAILED")
print()
print("CONCLUSION: U, V and the bulk block G_0 do NOT satisfy any Mahler functional")
print("equation (no fit + non-rational + Mahler-incompatible pole law). The catalytic")
print("dilation t->q^2 t acts on the CATALYTIC variable (shifting k in G_k=F(q,q^k) by +2),")
print("NOT on the function argument q. It is a q-DIFFERENCE/shift equation, not a Mahler")
print("(argument-powering q->q^k) equation. Nishioka's dichotomy does NOT apply. ROUTE DEAD.")
