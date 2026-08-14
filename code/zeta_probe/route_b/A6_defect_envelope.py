import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
maxK=mp.mpf(0); maxKm=0
for m in range(1,30):
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=40+int(1.1*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(55/(1-q))
    P12,Se,P11,P21=cocycle(q,N); sw=mp.sin(w)
    d11=abs(P11/(w*sw)-1)/tau; dSe=abs(Se*w/sw-1)/tau
    k=max(d11,dSe)
    if k>maxK: maxK=k; maxKm=m
    mp.mp.dps=30
print(f"max(|d11|,|dSe|)/tau over m=1..29 = {float(maxK):.6f} at m={maxKm}  (need < 1/6=0.1667 for s0=1/2 gate)")
print(f"  => K={float(maxK):.4f} < 1/6: same-class O(tau) defect envelope closes gate. PASS: {maxK<mp.mpf(1)/6}")
