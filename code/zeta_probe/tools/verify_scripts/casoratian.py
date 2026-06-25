import mpmath as mp
mp.mp.dps = 40
# Morita's q-difference equation for u=J^{(3)}_nu(x;q):
#   u(xq) - {(q^{nu/2}+q^{-nu/2}) - q^{-nu/2+1} x^2} u(x q^{1/2}) + u(x) = 0
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
nu=mp.mpf(3)/2; tau=mp.mpf('0.1'); q=mp.e**(-tau)
def B(x): return (q**(nu/2)+q**(-nu/2)) - q**(-nu/2+1)*x*x
print("(1) Does J^(3)_nu satisfy Morita's q-difference equation?  residual should be ~0:")
for xf in [0.3,0.5,0.8,1.2]:
    x=mp.mpf(xf)
    res = J3(nu,x*q,q) - B(x)*J3(nu,x*mp.sqrt(q),q) + J3(nu,x,q)
    print(f"   x={xf}:  residual = {mp.nstr(res,4)}")
print()
print("(2) Casoratian C_n = u_{n+1} v_n - u_n v_{n+1} EXACTLY constant for u_{n+1}+u_{n-1}=B_n u_n?")
# sample two independent solutions along x_n = x0 q^{n/2}; u=J3_{3/2}, v=J3_{-1/2} (independent)
x0=mp.mpf('1.0')
def seq(nu_, M):
    return [J3(nu_, x0*q**(mp.mpf(n)/2), q) if nu_>0 else
            J3(mp.mpf(1)/2, x0*q**(mp.mpf(n)/2), q) for n in range(M)]
M=8
u=[J3(nu, x0*q**(mp.mpf(n)/2), q) for n in range(M)]
v=[J3(mp.mpf(1)/2, x0*q**(mp.mpf(n)/2), q) for n in range(M)]   # second solution (different order)
print("   C_n for n=0..6:")
for n in range(M-1):
    Cn=u[n+1]*v[n]-u[n]*v[n+1]
    print(f"     C_{n} = {mp.nstr(Cn,12)}")
