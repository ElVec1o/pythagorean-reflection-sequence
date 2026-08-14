"""
Pin down the orders of 1/P11 and Se at the pole, and whether the D6 summary's
"A_lead=0.3246, B_lead=-0.1478" decomposition is meaningful.

P12 = 1/P11 - Se.  From (P5): both 1/P11 and Se ~ const/sqrt(tau) (NOT tau^{3/2}!).
So the "A_lead t^{3/2}" framing in the summary is suspect. Find the TRUE leading
orders of 1/P11 and Se and their difference.
"""
import mpmath as mp

def cocycle_full(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return X,Y,x,y

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S

def refine_pole(q0, iters=8):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
half=mp.mpf('0.5')

print("="*100)
print("TRUE ORDERS of 1/P11 and Se at the pole, and the difference structure")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'Se*sqrt(t)':>13} {'(1/P11)*sqrt(t)':>16} {'sin(w)':>10} {'Se/(sqt/2 sinw)':>16}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=45+int(2.5*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22
    # Se ~ sqrt(tau/2) sin w  (fact 5 says Se ~ sqrt(tau/2) sin w)
    sef = Se*mp.sqrt(tau)
    invf = (1/P11)*mp.sqrt(tau)
    sw=mp.sin(w)
    se_check = Se/(mp.sqrt(tau/2)*sw)
    print(f"{m:>3} {float(tau):>11.4e} {float(sef):>13.7f} {float(invf):>16.7f} {float(sw):>10.5f} {float(se_check):>16.9f}")
    mp.mp.dps=50

print("\nNOTE: if Se ~ sqrt(tau/2) sin w and 1/P11 ~ 1/(w sin w R11) ~ sqrt(tau/2)/sin w (since w=sqrt(2/tau)),")
print("then BOTH 1/P11 and Se are O(sqrt tau), and P12 = 1/P11 - Se is their O(tau^{3/2}) difference.")

print("\n"+"="*100)
print("Is the D6 summary's 'A_lead=0.3246, B_lead=-0.1478' meaningful? Test the SCALED difference")
print("Define a = (1/P11)/sqrt(tau), b = Se/sqrt(tau).  a,b -> same const? a-b -> 0 like tau?")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'a=(1/P11)/sqt':>15} {'b=Se/sqt':>13} {'a-b':>13} {'(a-b)/tau':>12}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=45+int(2.5*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22
    a=(1/P11)/mp.sqrt(tau); b=Se/mp.sqrt(tau)
    print(f"{m:>3} {float(tau):>11.4e} {float(a):>15.9f} {float(b):>13.9f} {float(a-b):>13.3e} {float((a-b)/tau):>12.7f}")
    mp.mp.dps=50
print("\n  -> (a-b)/tau should -> 1/(4 sqrt2) = %.7f  if P12=(1/P11-Se)=O(tau^{3/2})=(a-b)sqrt(tau)" % float(1/(4*mp.sqrt(2))))
