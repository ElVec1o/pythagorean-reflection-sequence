"""
ADVERSARIAL PART 4: nail the ORDER of the remainders, and decide V-footing vs named-fact.

The reduction chain (all exact except the two asymptotic inputs):
  t1 = P12/Se,  P12 = E + R,  Se = E_S + R_S,   E=(1/2)(w-W)^2 sinw sin(w-W),  E_S=sinw sin(w-W).
  t1 = (E/E_S) * (1 + R/E)/(1 + R_S/E_S),   E/E_S = (1/2)(w-W)^2 = tau/4 * [exact elementary].
R2 closes ON V's FOOTING iff R/E -> 0 and R_S/E_S -> 0 follow from the lem:cos O(.) BOUND ALONE
(no new saddle constant). lem:cos bound = |Se - E_S| = O(tau) and the companion |P12 - E| = O(tau^2)?
We MEASURE the orders. If R = O(tau^2) and E ~ tau^{3/2}, then R/E = O(tau^{1/2}) -> 0 by a BOUND, no constant needed.
If R/E only -> 0 like measured but R is NOT O(tau^2) (e.g. R ~ c*tau^2 with c needing a saddle), that is the named fact.

KEY adversarial point: is the BOUND |P12-E|=O(tau^2) of the SAME TYPE as lem:cos (i.e. follows from
lem:Bbounded / the steepest-descent O() bound), or is it an INDEPENDENT estimate on the SINE-partner of Se?
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

print("="*112)
print("PART 4  --  ORDERS of the remainders R=P12-E and R_S=Se-E_S at travel poles.")
print("  E ~ (1/4 sqrt2) tau^{3/2} sinw,  E_S ~ sqrt(1/2) tau^{1/2} sinw.   sinw=+-1 at poles.")
print("  If R/tau^2 bounded => R/E = O(tau^{1/2}); if R_S/tau bounded => R_S/E_S = O(tau^{1/2}). Then BOUND suffices.")
print("="*112)
print(f"{'m':>3} {'tau':>10} {'sinw':>5} | {'R=P12-E':>12} {'R/tau^2':>10} {'R/E':>10} {'R/E /sqrt(tau)':>13} | {'R_S':>12} {'R_S/tau':>9} {'R_S/E_S /sqrt(tau)':>17}")
for m in [2,4,8,16,24,32,40,48,56]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=70+int(2.6*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(70/(1-q))
    W=w*mp.e**(-tau/2)
    P12,Se,P11,P21=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*sw*swW; ES=sw*swW
    R=P12-E; RS=Se-ES
    rE=R/E; rSE=RS/ES
    print(f"{m:>3} {float(tau):>10.3e} {float(sw):>5.1f} | {float(R):>12.4e} {float(R/tau**2):>10.5f} {float(rE):>10.3e} {float(rE/mp.sqrt(tau)):>13.6f} | {float(RS):>12.4e} {float(RS/tau):>9.5f} {float(rSE/mp.sqrt(tau)):>17.6f}")
    mp.mp.dps=70
print()
print("READING:")
print("  R/tau^2 -> a finite constant  => R=O(tau^2), and since E~tau^{3/2}, R/E=O(sqrt tau) -> 0.")
print("  R/E /sqrt(tau) -> a finite constant  CONFIRMS R/E = Theta(sqrt tau) (a genuine O(sqrt tau) bound, NOT smaller).")
print("  R_S/tau -> finite constant => R_S=O(tau)=lem:cos T2-class; R_S/E_S=O(sqrt tau).")
print()
print("="*112)
print("PART 5  --  FULL reconstruction of t1 from the ELEMENTARY ratio + measured corrections (sanity).")
print("  t1_recon = (1/2)(w-W)^2 * (1+R/E)/(1+R_S/E_S)  vs  t1 = P12/Se exact (must match to machine eps).")
print("="*112)
print(f"{'m':>3} {'tau':>10} {'t1=P12/Se':>13} {'t1_recon':>13} {'match':>8} {'(1/2)(w-W)^2':>14} {'/(tau/4)':>10}")
for m in [2,8,24,48]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=70+int(2.6*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(70/(1-q))
    W=w*mp.e**(-tau/2)
    P12,Se,P11,P21=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*sw*swW; ES=sw*swW
    R=P12-E; RS=Se-ES
    t1=P12/Se
    t1rec=(mp.mpf(1)/2*(w-W)**2)*(1+R/E)/(1+RS/ES)
    ee=mp.mpf(1)/2*(w-W)**2
    print(f"{m:>3} {float(tau):>10.3e} {float(t1):>13.8f} {float(t1rec):>13.8f} {float(abs(t1-t1rec)):>8.1e} {float(ee):>14.8f} {float(ee/(tau/4)):>10.7f}")
    mp.mp.dps=70
