"""
Better-conditioned high-order a_n: collect MANY poles, fit NA coeffs by least-squares
(overdetermined), with extended precision. Reuse poles from prior runs if cached.
Caches (tau,f) pairs to /tmp/polefs.pkl keyed by m, reused across runs.
"""
import mpmath as mp, pickle, sys, os
CACHE='/tmp/polefs.pkl'
pf=pickle.load(open(CACHE,'rb')) if os.path.exists(CACHE) else {}  # m -> (taustr, fstr, dps)

def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1);n=0
    while True:
        S+=2*q/(1-q**(2*n+2))*pr
        pr*=2*q**(2*n+4)/(1-q**(2*n+3))-2*q**(2*n+3)/(1-q**(2*n+2))
        if n>5 and abs(pr)<mp.mpf(10)**(-mp.mp.dps-15): break
        n+=1
        if n>int(500/(1-q))+150: break
    return S
def pole_tau(m,dps):
    mp.mp.dps=dps
    phi=(m+mp.mpf(1)/2)*mp.pi; tau0=2/phi**2
    f=lambda t: Sig_t(mp.e**(-t))-1
    return mp.findroot(f,(tau0,tau0*mp.mpf('1.000001')),solver='secant',tol=mp.mpf(10)**(-(dps-20)))
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y
def f_at(m,dps):
    tau=pole_tau(m,dps); mp.mp.dps=dps
    q=mp.e**(-tau); w=mp.sqrt(2/tau); S=mp.sin(w)
    N=int(220/(1-q))
    P12,Se=cocycle(q,N)
    Y3_1=(1-q**3)*P12/(2*q**3); Y3_1oq=3*Y3_1-(1-q**(-3))*Se
    target=(3/mp.sqrt(2))*tau**mp.mpf('1.5')*S
    return tau, (Y3_1oq/target-1).real

MMAX=int(sys.argv[1]); NA=int(sys.argv[2])
ms=list(range(5,MMAX+1))
for m in ms:
    dps=90+int(1.6*m*m)
    if m in pf and pf[m][2]>=dps-5:
        continue
    tau,f=f_at(m,dps)
    pf[m]=(mp.nstr(tau,dps-10), mp.nstr(f,dps-10), dps)
    pickle.dump(pf,open(CACHE,'wb'))
    print(f"m={m} dps={dps} done",flush=True)

# least-squares fit: solve for a_1..a_NA using all poles m in ms with min dps
DPS=90+int(1.6*MMAX*MMAX)
mp.mp.dps=DPS
rows=[(mp.mpf(pf[m][0]), mp.mpf(pf[m][1])) for m in ms]
# overdetermined: use normal equations A^T A x = A^T b, A_{i,n}=tau_i^n
K=NA; M=len(rows)
# build normal equations
ATA=mp.matrix(K,K); ATb=mp.matrix(K,1)
for (tau,f) in rows:
    pows=[tau**n for n in range(1,K+1)]
    for i in range(K):
        ATb[i,0]+=pows[i]*f
        for j in range(K):
            ATA[i,j]+=pows[i]*pows[j]
sol=mp.lu_solve(ATA,ATb)
# also a pure square fit on the NA smallest-tau for agreement
sm=sorted(rows,key=lambda r:r[0])[:NA]
A=mp.matrix(NA,NA); b=mp.matrix(NA,1)
for i,(tau,f) in enumerate(sm):
    b[i,0]=f
    for n in range(1,NA+1): A[i,n-1]=tau**n
sol2=mp.lu_solve(A,b)
known={1:mp.mpf(2269)/1296,2:mp.mpf(507266513)/251942400,3:mp.mpf(2097873762713657)/1199951262720000}
out={}
print(f"\na_n (LSQ M={M} poles vs square NA={NA}; agreement=trusted):")
for n in range(1,NA+1):
    x1=sol[n-1,0]; x2=sol2[n-1,0]; d=abs(x1-x2)
    ag=DPS if d==0 else max(0,-int(mp.log10(d/(abs(x1)+mp.mpf(10)**(-DPS)))))
    out[n]=mp.nstr(x1,min(40,ag+3))
    e=f" kdiff={mp.nstr(x1-known[n],3)}" if n in known else ""
    print(f"  a_{n}={out[n]}  ag~{ag}{e}")
pickle.dump(out,open('/tmp/an_lsq.pkl','wb'))
print("saved")
