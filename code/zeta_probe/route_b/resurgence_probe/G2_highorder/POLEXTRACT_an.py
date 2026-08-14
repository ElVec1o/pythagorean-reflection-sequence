"""
HIGH-ORDER a_n via high-precision pole extraction + linear solve.
f(tau)=Y3(1/q)/[(3/sqrt2)tau^{3/2}sin w]-1 at poles (exact cocycle Y3).
Fit f = sum_{n=1}^{NA} a_n tau^n using NA poles (Vandermonde solve in tau).
Stability: vary NA and pole-set; report converged digits per a_n.
Saves a_n (mpf strings) to /tmp/an_highorder.pkl
"""
import mpmath as mp, pickle, sys

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
    N=int(200/(1-q))
    P12,Se=cocycle(q,N)
    Y3_1=(1-q**3)*P12/(2*q**3); Y3_1oq=3*Y3_1-(1-q**(-3))*Se
    target=(3/mp.sqrt(2))*tau**mp.mpf('1.5')*S
    return tau, Y3_1oq/target-1

# To get a_n to n=NA accurately, need poles spanning a range and dps high enough that
# the (NA)-term fit residual ~ tau^{NA+1} is resolvable. Use m up to MMAX, dps scaled.
NA=int(sys.argv[1]) if len(sys.argv)>1 else 14
MMAX=int(sys.argv[2]) if len(sys.argv)>2 else NA+10
ms=list(range(6, MMAX+1))
DPS=80+int(1.5*MMAX*MMAX)   # poles at large m need ~m^2 digits
data=[]
for m in ms:
    tau,f=f_at(m,DPS); data.append((mp.mpf(tau),mp.mpf(f.real if hasattr(f,'real') else f)))
    print(f"m={m} tau={mp.nstr(tau,6)} f={mp.nstr(f,12)}",flush=True)

mp.mp.dps=DPS
def fit(use):
    K=len(use)
    A=mp.matrix(K,K); b=mp.matrix(K,1)
    for i,(tau,f) in enumerate(use):
        b[i,0]=f
        for n in range(1,K+1): A[i,n-1]=tau**n
    return mp.lu_solve(A,b)
# fit with NA terms using the NA smallest-tau (largest-m) poles, and also NA using next set -> compare
sol1=fit(data[-NA:])
sol2=fit(data[-NA-1:-1]) if len(data)>=NA+1 else sol1
print("\na_n (two pole-sets, agreement = trusted digits):")
known={1:mp.mpf(2269)/1296,2:mp.mpf(507266513)/251942400,3:mp.mpf(2097873762713657)/1199951262720000}
an={}
for n in range(1,NA+1):
    a1=sol1[n-1,0]; a2=sol2[n-1,0] if n<=len(sol2) else a1
    d=abs(a1-a2)
    agree= mp.mp.dps if d==0 else max(0,-int(mp.log10(d/(abs(a1)+mp.mpf(10)**(-mp.mp.dps)))))
    an[n]=a1
    e=""
    if n in known: e=f" known diff={mp.nstr(a1-known[n],3)}"
    print(f"  a_{n}={mp.nstr(a1,min(30,agree+2))}  agree~{agree}dig{e}")
pickle.dump({n:mp.nstr(an[n],60) for n in an}, open('/tmp/an_highorder.pkl','wb'))
print(f"\nsaved {len(an)} coeffs (NA={NA}, MMAX={MMAX}, DPS={DPS})")
