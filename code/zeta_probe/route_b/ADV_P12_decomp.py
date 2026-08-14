"""
ADVERSARIAL test of the DECISIVE claim distinguishing the two contradictory
conclusions in memory:
  (gapless memory L81-88) P12 leading order = ELEMENTARY E=(1/2)(w-W)^2 sinw sin(w-W),
     remainder R=P12-E STRICTLY subleading: R/(tau^{3/2} sinw) -> 0.
     => R2 closes on lem:cos BOUND alone (V's footing).
  (gapless memory L116-123 + prompt summary) P12 needs the SADDLE CONSTANT
     (the sine partner of Se), one notch beyond the bound.

If R/(tau^1.5) -> 0 robustly, the elementary route stands and lem:Bbounded BOUND suffices.
If R/(tau^1.5) -> nonzero const, then a genuine saddle constant is needed.

Also: is E/E_S = (1/2)(w-W)^2 EXACT (algebraic), independent of any saddle?  YES by construction
(both E and E_S share the sinw sin(w-W) factor). The question is whether E is the TRUE leading
term of P12 (i.e. R subleading) -- THAT is the saddle/elementary question.
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x   # P12,P22=Se,P11,P21
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
print(f"{'m':>3} {'tau':>9} {'P12/tau^1.5':>12} {'E/tau^1.5':>12} {'R/tau^1.5':>12} {'R/E':>10} {'sinw':>6}")
for m in [1,2,4,8,16,24,32,40,48,56]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=55+int(2.0*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; N=int(70/p)
    W=w*mp.e**(-tau/2)
    P12,Se,P11,P21=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*sw*swW
    R=P12-E
    t15=tau**mp.mpf('1.5')
    print(f"{m:>3} {float(tau):>9.2e} {float(P12/t15):>12.7f} {float(E/t15):>12.7f} {float(R/t15):>12.3e} {float(R/E):>10.3e} {float(sw):>6.2f}",flush=True)
    mp.mp.dps=40
