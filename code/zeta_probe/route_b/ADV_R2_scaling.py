"""
Determine the tau-SCALING of the remainders R=P12-E and R_S=Se-E_S at the poles.
If R = O(tau^2) (so R/E=R/tau^1.5 ~ O(sqrt tau)) and R_S = O(tau) (so R_S/E_S ~ O(sqrt tau)),
then BOTH corrections vanish at rate O(sqrt tau) -- exactly the lem:cos BOUND character that
already closed R1.  Fit log|R| vs log tau and log|R_S| vs log tau across poles.

ALSO compare to R1's own correction: b0*tau-2 and So/Se-1 scalings, to confirm "same footing".
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
data=[]
ms=[4,8,12,16,20,24,28,32,36,40,44]
print(f"{'m':>3} {'tau':>10} {'|R|':>11} {'|R|/tau^2':>11} {'|R_S|':>11} {'|R_S|/tau':>11}")
for m in ms:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=55+int(2.2*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; N=int(70/p)
    W=w*mp.e**(-tau/2)
    P12,Se=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    ES=sw*swW; E=mp.mpf(1)/2*(w-W)**2*ES
    RS=Se-ES; R=P12-E
    data.append((float(mp.log(tau)),float(mp.log(abs(R))),float(mp.log(abs(RS)))))
    print(f"{m:>3} {float(tau):>10.3e} {float(abs(R)):>11.3e} {float(abs(R)/tau**2):>11.5f} {float(abs(RS)):>11.3e} {float(abs(RS)/tau):>11.5f}",flush=True)
    mp.mp.dps=40
# linear fit slope of log|R| vs log tau, and log|R_S| vs log tau
import statistics
def slope(xs,ys):
    n=len(xs); mx=sum(xs)/n; my=sum(ys)/n
    return sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
lt=[d[0] for d in data]
print(f"\nslope log|R| vs log tau   = {slope(lt,[d[1] for d in data]):.4f}  (expect ~2 if R=O(tau^2))")
print(f"slope log|R_S| vs log tau = {slope(lt,[d[2] for d in data]):.4f}  (expect ~1 if R_S=O(tau))")
