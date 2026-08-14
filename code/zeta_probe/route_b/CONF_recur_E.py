import mpmath as mp
mp.mp.dps=40
# verify the 3-term recursion gives the cocycle P12 (=Y col), and the Bessel approximant residual
def cocycle_cols(q,N):
    # y_{n+1}=(1+q^3-2(1-q)q^{2n+2})y_n - q^3 y_{n-1}; two columns from the 2x2 transfer
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=14):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# Bessel approximant for the SECOND solution Y3(1): Y3(1) -> (3/w^2)(sin w/w - cos w) (paper line 549, leading)
# and the SHIFTED W=w e^{-tau/2} version. Check both vs actual P12=(2q^3/(1-q^3))Y3(1).
print(f"{'m':>2}{'tau':>9}  P12 actual        E (elem)          ratio P12/E    leadBessel/P12")
for m in [2,4,6,8,10,14]:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    N=int((mp.mp.dps+15)*2.3026/tau)+60
    P12,Se=cocycle_cols(q,N)
    E=mp.mpf('0.5')*(w-W)**2*mp.sin(w)*mp.sin(w-W)
    # leading Bessel for Y3(1): (3/w^2)(sin w/w - cos w); P12=(2q^3/(1-q^3))Y3
    Y3lead=(3/w**2)*(mp.sin(w)/w-mp.cos(w))
    P12_bess=(2*q**3/(1-q**3))*Y3lead
    print(f"{m:>2}{float(tau):>9.5f}  {mp.nstr(P12,8):>14}  {mp.nstr(E,8):>14}  {float(P12/E):>12.6f}  {float(P12_bess/P12):>12.5f}")
