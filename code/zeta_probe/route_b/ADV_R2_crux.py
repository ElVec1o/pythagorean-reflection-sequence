"""
THE CRUX. Does the elementary E_S=sinw sin(w-W) reproduce Se's sqrt(tau) coefficient
INCLUDING the lem:cos saddle constant, or does it MISS it (so the saddle constant is needed)?

Known (lemcos/Task F): Se = cos W - T2 EXACT, T2 ~ (sqrt2/36) sqrt(tau) sin w (the saddle).
Also memory: E_S = sin w sin(w-W) is the "elementary phase shift", dominant sqrt(tau) part.
Question: at the pole, (Se - E_S)/(sqrt(tau) sin w) -> ?
  If -> 0: E_S captures full sqrt(tau), saddle constant NOT needed in leading t1 -> BOUND suffices.
  If -> nonzero c: E_S misses the saddle term; t1 leading would then need that constant.

We found R_S=Se-E_S ~ tau^1.5, i.e. (Se-E_S)/(sqrt tau) ~ tau -> 0.  Verify directly, and also
decompose: write Se = cosW - T2. Compare cosW vs E_S and -T2 contributions at the sqrt(tau) level.
Also confirm the SAME structure for P12: does its sqrt(tau)-partner saddle get absorbed by E?
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
print("Decompose Se and E_S at sqrt(tau) order. sw=sin w; sqt=sqrt(tau).")
print(f"{'m':>3} {'tau':>9} {'Se/(sqt*sw)':>12} {'E_S/(sqt*sw)':>12} {'cosW/(sqt*sw)':>13} {'(Se-E_S)/(sqt*sw)':>17}")
for m in [2,4,8,16,24,32,40,48]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=55+int(2.2*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; N=int(70/p)
    W=w*mp.e**(-tau/2)
    P12,Se=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W); cW=mp.cos(W)
    ES=sw*swW
    sqt=mp.sqrt(tau)
    norm=sqt*sw
    print(f"{m:>3} {float(tau):>9.2e} {float(Se/norm):>12.7f} {float(ES/norm):>12.7f} {float(cW/norm):>13.5f} {float((Se-ES)/norm):>17.3e}",flush=True)
    mp.mp.dps=40
print("\nNote: Se/(sqt sw) and E_S/(sqt sw) should -> 1/sqrt2=0.70711 (since Se~sqrt(tau/2) sin w).")
print("(Se-E_S)/(sqt sw) -> 0 would mean E_S captures the FULL sqrt(tau) Se incl saddle => BOUND suffices.")
