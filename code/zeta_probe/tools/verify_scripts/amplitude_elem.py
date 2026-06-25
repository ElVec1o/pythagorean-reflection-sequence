import mpmath as mp
mp.mp.dps = 40
def qpoch(a,q,n):
    r=mp.mpf(1)
    for k in range(n): r*=(1-a*q**k)
    return r
def qpoch_inf(a,q):
    r=mp.mpf(1);k=0
    while True:
        t=1-a*q**k;r*=t;k+=1
        if abs(t-1)<mp.mpf(10)**(-38) or k>200000: break
    return r
def J3(nu,x,q,N=160):
    pref=qpoch_inf(q**(nu+1),q)/qpoch_inf(q,q)
    s=mp.fsum((-1)**n*q**(mp.mpf(n*(n-1))/2)*(q*x*x)**n/(qpoch(q**(nu+1),q,n)*qpoch(q,q,n)) for n in range(N))
    return pref*x**nu*s
nu=mp.mpf(3)/2; tau=mp.mpf('0.06'); q=mp.e**(-tau); x0=mp.mpf('1.4')
def Bn(n):
    xn=x0*q**(mp.mpf(n)/2); return (q**(nu/2)+q**(-nu/2)) - q**(-nu/2+1)*xn*xn
M=16
u=[J3(nu, x0*q**(mp.mpf(n)/2), q) for n in range(M)]
G=lambda n: u[n]**2 - Bn(n)*u[n]*u[n+1] + u[n+1]**2   # = A_n^2 sin^2 psi_n
print("(A) EXACT identity  G_{n+1}-G_n = (B_n - B_{n+1}) u_{n+1} u_{n+2}  (residual ->0):")
for n in range(2,7):
    lhs=G(n+1)-G(n); rhs=(Bn(n)-Bn(n+1))*u[n+1]*u[n+2]
    print(f"   n={n}: residual = {mp.nstr(lhs-rhs,4)}")
print()
print("(B) envelope law  A_n (4-B_n^2)^{1/4} = const (1+O(tau))   [A_n = sqrt(G_n)/sin psi_n]:")
vals=[]
for n in range(2,11):
    B=Bn(n)
    if abs(B)<2:
        psi=mp.acos(B/2); An=mp.sqrt(G(n))/mp.sin(psi)
        inv=An*(4-B*B)**mp.mpf('0.25')
        vals.append(inv)
        print(f"   n={n}: A_n (4-B^2)^(1/4) = {mp.nstr(inv,10)}")
sp=(max(vals)-min(vals))/abs(vals[0])
print(f"   relative spread over the oscillatory bulk = {mp.nstr(sp,3)}  (~tau={float(tau)} => O(tau), x-independent envelope)")
