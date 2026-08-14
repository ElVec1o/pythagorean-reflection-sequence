import mpmath as mp
mp.mp.dps=50
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y
def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(300/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=18):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
ms=[8,12,16,20,26,32,40,50]
xs=[];ys=[]
for m in ms:
    q=refine(poles[m-1]);tau=-mp.log(q);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    N=int((mp.mp.dps+15)*2.3026/tau)+80
    P12,Se=cocycle(q,N)
    E=mp.mpf('0.5')*(w-W)**2*mp.sin(w)*mp.sin(w-W)
    val=(P12/E-1)/tau
    xs.append(tau);ys.append(val)
    print(f"m={m:>2} tau={float(tau):.6f}  (P12/E-1)/tau={mp.nstr(val,16)}")
# Richardson / polynomial extrapolation to tau->0: fit ys = c0 + c1 tau + c2 tau^2 ... (Vandermonde, few points)
n=len(xs)
A=mp.matrix(n,n);b=mp.matrix(n,1)
for i in range(n):
    p=mp.mpf(1)
    for j in range(n): A[i,j]=p; p*=xs[i]
    b[i]=ys[i]
c=mp.lu_solve(A,b)
c0=c[0]
print(f"\nExtrapolated c = lim (P12/E-1)/tau = {mp.nstr(c0,20)}")
print(f"  candidates: 35/24={mp.nstr(mp.mpf(35)/24,12)}  7/4-... ; identify:")
for cand,name in [(mp.mpf(35)/24,'35/24'),(mp.mpf(7)/4-mp.mpf(1)/3,'7/4-1/3=17/12'),(mp.mpf(1)+mp.mpf(11)/24,'1+11/24=35/24'),(mp.mpf(105)/72,'105/72')]:
    print(f"    {name} = {mp.nstr(cand,12)}  diff={mp.nstr(c0-cand,4)}")
rid=mp.identify(c0,['pi','sqrt(2)'])
print(f"  mp.identify(c0)={rid}")
print(f"  c0*0.5/sqrt2-check: R/tau^2.5 const = c0*|E|/tau^1.5 leading = c0*(1/(4 sqrt2)) = {mp.nstr(c0/(4*mp.sqrt(2)),8)} (known 0.258)")
