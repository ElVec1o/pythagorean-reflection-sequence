import mpmath as mp, pickle, numpy as np
mp.mp.dps=60
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]

# Prony with K exponentials: b_n ~ sum_{j} C_j r_j^n, singularities A_j=1/r_j.
# Solve for the recurrence of order K via least-squares Hankel, find all roots.
def prony(K, nmax):
    # rows n=K..nmax: sum_{i=1}^K c_i b_{n-i} = b_n  (monic poly x^K - sum c_i x^{K-i})
    rows=[]; rhs=[]
    for n in range(K, nmax+1):
        rows.append([b[n-i] for i in range(1,K+1)])
        rhs.append(b[n])
    Mt=mp.matrix(rows); rv=mp.matrix(rhs)
    # least squares via normal equations
    MtT=Mt.T
    NM=MtT*Mt; Nr=MtT*rv
    c=mp.lu_solve(NM,Nr)
    coeffs=[mp.mpf(1)]+[-c[i] for i in range(K)]  # x^K - c1 x^{K-1} - ...
    roots=mp.polyroots(coeffs, maxsteps=200, extraprec=100)
    sings=sorted([1/r for r in roots], key=lambda z: abs(z))
    return sings

for K in [2,3,4,5]:
    try:
        s=prony(K, Nrel)
        print(f"\nK={K} Prony, nearest {min(K,4)} singularities (by |.|):")
        for z in s[:4]:
            z=mp.mpc(z)
            print(f"   |A|={float(abs(z)):8.4f}  arg={float(mp.arg(z)*180/mp.pi):+8.2f}  Re={float(z.real):7.3f} Im={float(z.imag):7.3f}")
    except Exception as e:
        print("K=",K,"fail",e)
