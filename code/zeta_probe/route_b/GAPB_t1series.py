"""
OPTION 2 test: is t1(tau)=P12/Se (at poles) a CONVERGENT series (radius>tau_1=0.09) or ASYMPTOTIC?
If convergent => s(tau)=(q/p)t1 analytic, s<1 on (0,tau_1] follows from bounding the series => BYPASSES Olver.
Compute t1(q_m)/tau at poles m=1..12 (high dps), Vandermonde-fit the coeffs c_k of t1/tau=sum c_k tau^k,
report |c_k| growth (radius=1/limsup|c_k|^{1/k}; factorial=>asymptotic, geometric=>convergent), and TEST
convergence: partial sums at tau_1=0.09 vs the actual t1(q_1)/tau_1.
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x   # P12,Se,P11,P21
def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1); maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2))-2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S
def refine(q0,it=14):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h); dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
mp.mp.dps=120
taus=[]; vals=[]
for m in range(1,13):
    q=refine(poles[m-1]); tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(80/(1-q))
    P12,Se,P11,P21=cocycle(q,N); t1=P12/Se
    taus.append(tau); vals.append(t1/tau)   # t1/tau
# Vandermonde fit: t1/tau = sum_{k=0}^{K} c_k tau^k, K=len-1
K=len(taus)-1
A=mp.matrix(K+1,K+1); b=mp.matrix(K+1,1)
for i in range(K+1):
    for j in range(K+1): A[i,j]=taus[i]**j
    b[i]=vals[i]
c=mp.lu_solve(A,b)
print("Fitted coeffs c_k of t1/tau = sum c_k tau^k  (known: 1/4,3/16,13/96,13/256,-629/7680):")
known=[mp.mpf(1)/4,mp.mpf(3)/16,mp.mpf(13)/96,mp.mpf(13)/256,-mp.mpf(629)/7680]
for k in range(min(8,K+1)):
    kn = float(known[k]) if k<len(known) else None
    print(f"  c_{k} = {float(c[k]):+.7f}" + (f"   known {kn:+.7f}" if kn is not None else "")
          + (f"   |c_{k}|^(1/{k})={float(abs(c[k])**(mp.mpf(1)/k)):.3f}" if k>=1 else ""))
print("\nRatios |c_{k+1}/c_k| (->1/radius; bounded=>convergent, growing=>asymptotic):")
for k in range(1,min(7,K)):
    if c[k]!=0: print(f"  |c_{k+1}/c_{k}| = {float(abs(c[k+1]/c[k])):.4f}")
print("\nConvergence test at tau_1=%.5f (largest pole): partial sums vs actual t1/tau=%.8f" % (float(taus[0]),float(vals[0])))
for K2 in [2,4,6,8,10]:
    ps=sum(c[k]*taus[0]**k for k in range(min(K2+1,K+1)))
    print(f"  sum_{{0..{K2}}} = {float(ps):.8f}   resid={float(abs(ps-vals[0])):.2e}")
print("\nIf resid DECREASES with more terms => CONVERGENT at tau_1 => Option 2 viable (radius>tau_1).")
print("If ratios bounded ~2 => radius~1/2>0.09 => s(tau)=(q/p)t1 analytic, s<1 provable from the series.")
