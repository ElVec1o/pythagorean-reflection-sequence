"""
PART 6: precision-clean order determination + cross-check against the KNOWN lem:cos reference.
Known (from gapless memory + SYNTH_transfer): Se = cos W - T2 EXACT (T1 cancels), T2=lem:cos saddle ~ (sqrt2/36)sqrt(tau) sinw.
At a pole, w=w_m with sin w=+-1, cos w=O(sqrt tau). W=w e^{-tau/2}.
Elementary references used in CLAIM-A: E_S = sin w sin(w-W),  E = (1/2)(w-W)^2 sin w sin(w-W).
We (a) push dps high enough that R=P12-E is trustworthy at large m, (b) fit the ORDER of R and R_S by log-log slope,
(c) cross-check E_S vs cos W (are they the same leading object?).
"""
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

print("="*110)
print("PART 6  --  precision-clean (high dps, N=120/p) orders of R=P12-E, R_S=Se-E_S; log-log slopes.")
print("="*110)
data=[]
for m in [4,8,12,16,20,24,28,32]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=90+int(3.2*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(120/(1-q))
    W=w*mp.e**(-tau/2)
    P12,Se,P11,P21=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*sw*swW; ES=sw*swW
    R=P12-E; RS=Se-ES
    cosW=mp.cos(W)
    data.append((float(tau),abs(float(R)),abs(float(RS)),float(R/E),float(RS/ES),float(ES),float(cosW),float(ES/cosW)))
    print(f"m={m:>3} tau={float(tau):.3e}  R={float(R):+.4e} R_S={float(RS):+.4e}  R/E={float(R/E):+.3e} R_S/E_S={float(RS/ES):+.3e}  E_S={float(ES):.4e} cosW={float(cosW):.4e} E_S/cosW={float(ES/cosW):.5f}")
    mp.mp.dps=90
# log-log slopes (order in tau)
import math
def slope(xs,ys):
    # fit log|y| = a*log(x)+b, return a over last few clean points
    lx=[math.log(x) for x in xs]; ly=[math.log(abs(y)) for y in ys]
    n=len(lx); sx=sum(lx); sy=sum(ly); sxx=sum(t*t for t in lx); sxy=sum(lx[i]*ly[i] for i in range(n))
    return (n*sxy-sx*sy)/(n*sxx-sx*sx)
taus=[d[0] for d in data]; Rs=[d[1] for d in data]; RSs=[d[2] for d in data]
print()
print(f"  log-log slope of |R|   vs tau (order p s.t. R~tau^p):  {slope(taus,Rs):.3f}")
print(f"  log-log slope of |R_S| vs tau (order):                {slope(taus,RSs):.3f}")
print(f"  [E ~ tau^1.5, E_S ~ tau^0.5.  R/E->0 needs slope(R)>1.5 ; R_S/E_S->0 needs slope(R_S)>0.5.]")
print()
print("  E_S/cosW column: if ->1, then E_S=sinw sin(w-W) and cosW share the SAME leading sqrt(tau) part")
print("  (they should: cos W = cos w cos W + sin w sin W... at pole cos w~0 so cosW ~ sin w sinW ~ E_S). Confirms E_S is the elementary cosW-class object, i.e. lem:cos territory, NOT a new saddle.")
