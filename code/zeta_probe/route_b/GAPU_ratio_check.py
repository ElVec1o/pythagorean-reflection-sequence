"""
GAP-U crux: is the gate s<1 carried by the ELEMENTARY leading t1~tau/4 (saddle cancels in the ratio
t1=P12/Se), with the residual R=P12-E needing only DECAY?  Or does it need the sharp saddle value?
Compute at poles:
  t1=P12/Se, t1/tau (->1/4?),  s=(q/p)t1 (->1/4?, gate s<1),
  E=(1/2)(w-W)^2 sin w sin(w-W) [elementary leading of P12],  R=P12-E,  R/tau^2 (->const => R=O(tau^2)),
  and the relative correction to s from R: dscorr=(q/p)(R/Se)/(1/4) -> 0 ?
If t1/tau->1/4 (elementary) and R=O(tau^2) (so dscorr->0), the gate s<1 holds with 4x margin on DECAY of R.
Scalar mpmath. m=1..18 (cocycle feasible). dps scales.
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x   # P12,Se,P11,P21
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print(f"{'m':>3}{'tau':>10}{'t1/tau':>10}{'s=(q/p)t1':>11}{'E/P12':>9}{'R/tau^2':>10}{'dscorr':>10}{'s<1?':>6}")
for m in range(1,19):
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=40+int(1.3*float(w)); N=int(60/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    W=w*mp.e**(-tau/2); sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf('0.5')*(w-W)**2*sw*swW        # elementary leading of P12
    R=P12-E
    t1=P12/Se; s=(q/p)*t1
    dscorr=(q/p)*(R/Se)/(mp.mpf(1)/4)      # relative correction to s from R (->0 => decay suffices)
    print(f"{m:>3}{float(tau):>10.6f}{float(t1/tau):>10.6f}{float(s):>11.6f}{float(E/P12):>9.5f}{float(R/tau**2):>10.5f}{float(dscorr):>10.2e}{str(s<1):>6}")
    mp.mp.dps=30
print("\nIf t1/tau->1/4=0.25 (elementary leading) and R/tau^2 bounded (R=O(tau^2)) and dscorr->0:")
print("=> gate s<1 holds at s->1/4 (4x margin) needing only the ELEMENTARY leading + DECAY of R.")
print("   The decay of R (parallel q-Bessel/saddle-class) is the lone input; the 4x margin absorbs degradation.")
