#!/usr/bin/env python3
"""
A_U =? A_V via residue amplitudes at KNOWN poles, robust version:
 (1) peel dominant pole: c0 = lim coeff_n / r0^n (exact coeffs, high precision).
 (2) least-squares fit of {c0,c1} (dominant travel r0=1.4916, bulk-dominant r1=1.2808)
     over a COMMON window n in [nlo,nhi] for BOTH U and V (systematic errors cancel in ratio).
 (3) compare c1^U/c1^V (bulk-dominant pole) and c0^U/c0^V (dominant, should be ~0.80).
Also a 3-pole fit adding r2 (travel q=0.9135) where conditioning allows.
"""
import mpmath as mp, json, os
mp.mp.dps=80
HERE=os.path.dirname(os.path.abspath(__file__))
V=[mp.mpf(s) for s in json.load(open(os.path.join(HERE,'V130.json')))]
U=[mp.mpf(x) for x in [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
   11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,
   2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]]

# precise frequencies r=1/sqrt(q): dominant travel, bulk-dominant, 2nd travel
r0=1/mp.sqrt(mp.mpf('0.4494536305589'))   # 1.49161778...
r1=1/mp.sqrt(mp.mpf('0.6095673442'))      # 1.28082...
r2=1/mp.sqrt(mp.mpf('0.9134866387'))      # 1.04628...

def lstsq_fit(coeffs, rs, nlo, nhi):
    K=len(rs); rows=nhi-nlo+1
    A=mp.matrix(rows,K); b=mp.matrix(rows,1)
    for i in range(rows):
        n=nlo+i
        for m in range(K): A[i,m]=rs[m]**n
        b[i,0]=coeffs[n]
    # normal equations (weighted by 1/r0^n to avoid overflow dominance): divide each row by r0^n
    for i in range(rows):
        n=nlo+i; s=r0**n
        for m in range(K): A[i,m]/=s
        b[i,0]/=s
    AT=A.T
    return mp.lu_solve(AT*A, AT*b)

print("Dominant-amplitude convergence c0 = coeff_n / r0^n (last few n):")
for arr,name in [(V,'V'),(U,'U')]:
    N=len(arr)
    vals=[arr[n]/r0**n for n in range(N-4,N)]
    print(f"  {name}: "+", ".join(mp.nstr(v,10) for v in vals))

print("\n--- 2-pole least-squares fit on COMMON window n in [25,42] (r0 travel, r1 bulk) ---")
for nlo,nhi in [(25,42),(30,42),(20,42)]:
    cV=lstsq_fit(V,[r0,r1],nlo,nhi); cU=lstsq_fit(U,[r0,r1],nlo,nhi)
    print(f" window[{nlo},{nhi}]:  c0^V={mp.nstr(cV[0,0],8)} c1^V={mp.nstr(cV[1,0],8)} | "
          f"c0^U={mp.nstr(cU[0,0],8)} c1^U={mp.nstr(cU[1,0],8)}")
    print(f"     ratios:  c0^U/c0^V={mp.nstr(cU[0,0]/cV[0,0],7)}  (expect ~0.80)   "
          f"c1^U/c1^V={mp.nstr(cU[1,0]/cV[1,0],7)}  (bulk pole)")

print("\n--- 3-pole fit (add r2 travel q=0.9135), window [18,42] ---")
for nlo,nhi in [(18,42),(22,42)]:
    cV=lstsq_fit(V,[r0,r1,r2],nlo,nhi); cU=lstsq_fit(U,[r0,r1,r2],nlo,nhi)
    print(f" window[{nlo},{nhi}]: ratios c0:{mp.nstr(cU[0,0]/cV[0,0],6)} c1(bulk):{mp.nstr(cU[1,0]/cV[1,0],6)} c2(trav.9135):{mp.nstr(cU[2,0]/cV[2,0],6)}")

print("\nINTERPRETATION: dominant c0 ratio ~0.80 (known). If c1,c2 ratios are LARGER (closer to 1)")
print("and trend up as the pole approaches 1, that supports A_U=A_V (defect subleading at poles).")
