#!/usr/bin/env python3
"""
DECISIVE TEST of  A_U = A_V  (U and V share leading residue amplitude at the accumulating poles).
Blind Pade fails on U (43 terms). But we KNOW the pole locations (roots of Sigma_1=1 travel and
S_1=1 bulk). Fitting residue AMPLITUDES at FIXED frequencies r_m=1/sqrt(q_m) is well-conditioned.

v_n ~ sum_m c_m^V r_m^n,  u_n ~ sum_m c_m^U r_m^n.  Compare c_m^U/c_m^V across poles:
  - dominant travel pole (q=0.4495, r=1.4916): expect c^U/c^V = lim u_n/v_n = 0.80 (known).
  - secondary poles (q->1): conjecture A_U=A_V => ratio -> 1 as pole -> 1.
If the ratios INCREASE from 0.80 toward 1 as the pole approaches 1, that is direct evidence the
connectivity defect is subleading at the accumulating poles (A_D->0, A_U=A_V).
"""
import mpmath as mp, json, os
mp.mp.dps=60
HERE=os.path.dirname(os.path.abspath(__file__))

V=[mp.mpf(s) for s in json.load(open(os.path.join(HERE,'V130.json')))]   # 131 terms
U=[mp.mpf(x) for x in [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
   11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,
   2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]]
print(f"V: {len(V)} terms, U: {len(U)} terms")

# pole locations
def Ak(k,q): return 2*q/(1-q**(k+1))
def Ck(k,q): return 2*q**(k+3)/(1-q**(k+2))-2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=3000):
    t=mp.mpf(0); p=mp.mpf(1)
    for j in range(J):
        t+=Ak(k+2*j,q)*p; p*=Ck(k+2*j,q)
        if abs(p)<mp.mpf(10)**(-80) and j>40: break
    return t
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2))-2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=3000):
    t=mp.mpf(0); p=mp.mpf(1)
    for j in range(J):
        t+=al(k+2*j,q)*p; p*=ga(k+2*j,q)
        if abs(p)<mp.mpf(10)**(-80) and j>40: break
    return t
def bis(f,a,b,it=200):
    fa=f(a)
    for _ in range(it):
        m=(a+b)/2
        if mp.sign(f(m))==mp.sign(fa): a=m
        else: b=m
    return (a+b)/2
def poles(g,n,w0=1.4):
    R=[]; w=mp.mpf(w0); pv=None; pq=None
    while len(R)<n and w<30:
        q=mp.e**(-2/w**2); v=g(q)-1
        if pv is not None and mp.sign(v)!=mp.sign(pv):
            R.append(bis(lambda qq:g(qq)-1,pq,q))
        pv=v; pq=q; w+=mp.mpf('0.04')
    return R
travel=poles(lambda q:Sig(1,q),4)
bulk=poles(lambda q:Sb(1,q),4)
print("travel poles q:",[mp.nstr(r,8) for r in travel])
print("bulk   poles q:",[mp.nstr(r,8) for r in bulk])

# build a sorted pole list by frequency r=1/sqrt(q) (descending), tag family
allp=[(q,'T') for q in travel]+[(q,'B') for q in bulk]
allp=[(q,fam,1/mp.sqrt(q)) for (q,fam) in allp]
allp.sort(key=lambda t:-t[2])
print("\npoles by frequency r=1/sqrt(q) (descending):")
for q,fam,r in allp: print(f"  {fam} q={mp.nstr(q,7)}  x={mp.nstr(mp.sqrt(q),7)}  r={mp.nstr(r,8)}")

def fit(coeffs, rs, n_lo):
    """solve sum_m c_m r_m^n = coeffs[n] for n=n_lo..n_lo+K-1 (K=len(rs))."""
    K=len(rs)
    M=mp.matrix(K,K); b=mp.matrix(K,1)
    for i in range(K):
        n=n_lo+i
        for m in range(K): M[i,m]=rs[m]**n
        b[i,0]=coeffs[n]
    c=mp.lu_solve(M,b)
    return [c[m,0] for m in range(K)]

# Use the K strongest poles. Fit V at large n, U at the largest n it has.
for K in [2,3]:
    rs=[allp[m][2] for m in range(K)]
    fams=[allp[m][1] for m in range(K)]; qs=[allp[m][0] for m in range(K)]
    cV=fit(V, rs, len(V)-K-2)
    cU=fit(U, rs, len(U)-K-1)
    print(f"\n=== K={K} poles fit ===")
    print(f"{'pole':>4} {'q':>10} {'c^V':>16} {'c^U':>16} {'c^U/c^V':>11}")
    for m in range(K):
        ratio = cU[m]/cV[m] if cV[m]!=0 else mp.nan
        print(f"{fams[m]:>4} {mp.nstr(qs[m],7):>10} {mp.nstr(cV[m],9):>16} {mp.nstr(cU[m],9):>16} {mp.nstr(ratio,7):>11}")
    print("  (dominant ratio should be ~0.80 = lim u_n/v_n; secondary ratios -> 1 supports A_U=A_V)")
