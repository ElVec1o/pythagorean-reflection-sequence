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
worst=mp.mpf(0); worstm=0; thr=1/mp.sqrt(2)
ms=list(range(1,len(poles)+1,2))  # every other pole to keep it fast
for m in ms:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=35+int(1.1*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(52/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    r=abs(P12)/tau**mp.mpf('1.5')
    if r>worst: worst=r; worstm=m
    mp.mp.dps=30
print(f"GATE SWEEP m=1,3,...,{ms[-1]} ({len(ms)} poles): worst |P12|/tau^1.5 = {float(worst):.6f} at m={worstm}")
print(f"  threshold 1/sqrt2 = {float(thr):.6f}; margin factor = {float(thr/worst):.2f}x. ALL pass: {worst<thr}")
