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
nu=mp.mpf(3)/2; tau=mp.mpf('0.08'); q=mp.e**(-tau)
x0=mp.mpf('1.3')
def Bn(n): # potential at x_n = x0 q^{n/2}: recurrence u_{n+2} = B_n u_{n+1} - u_n,  B_n=B(x_n)
    xn=x0*q**(mp.mpf(n)/2)
    return (q**(nu/2)+q**(-nu/2)) - q**(-nu/2+1)*xn*xn
M=14
u=[J3(nu, x0*q**(mp.mpf(n)/2), q) for n in range(M)]
# (a) verify recurrence u_{n+2} = B_n u_{n+1} - u_n
print("(a) recurrence residual u_{n+2}-B_n u_{n+1}+u_n:")
print("   ", [mp.nstr(u[n+2]-Bn(n)*u[n+1]+u[n],3) for n in range(4)])
# (b) second solution v by the SAME recurrence, v_0=0,v_1=1
v=[mp.mpf(0),mp.mpf(1)]
for n in range(M-2): v.append(Bn(n)*v[n+1]-v[n])
print("(b) Casoratian C_n = u_{n+1} v_n - u_n v_{n+1} (should be EXACTLY constant):")
Cs=[u[n+1]*v[n]-u[n]*v[n+1] for n in range(M-1)]
print("   ", [mp.nstr(c,10) for c in Cs[:7]])
print(f"    spread = {mp.nstr(max(Cs)-min(Cs),3)}  (->0 confirms the conserved Casoratian)")
# (c) amplitude law A_n = sqrt|C| (4-B_n^2)^{-1/4} (1+O(tau)) in oscillatory regime |B_n|<2.
#     extract A_n^2 from the pair (u,v): A_n^2 = (u_n^2 + v_n^2 ... ) ; use envelope via u_n,u_{n+1}:
#     for u_n=A cos(phi_n): A_n^2 ~ (u_n^2 - 2 (B_n/2) u_n u_{n+1} + u_{n+1}^2)/sin^2 psi_n
print("(c) amplitude law check: A_n^2 sin(psi_n) vs |C|/2  (psi_n=arccos(B_n/2)); ratio ->1:")
C=abs(Cs[3])
for n in range(2,9):
    B=Bn(n)
    if abs(B)<2:
        psi=mp.acos(B/2)
        A2=(u[n]**2 - B*u[n]*u[n+1] + u[n+1]**2)/mp.sin(psi)**2
        print(f"   n={n}: B_n={mp.nstr(B,5)} (osc)  A_n^2 sin psi /(|C|/2) = {mp.nstr(A2*mp.sin(psi)/(C/2),8)}")
    else:
        print(f"   n={n}: B_n={mp.nstr(B,5)} (non-osc, |B|>2)")
