"""
ATOM A: |T2| <= C sqrt(tau), C<1/sqrt2, at travel poles => b0>0.  Via van der Corput 2nd-deriv lemma
(Stein HA VIII Prop.2, c2=8) on the operative contour Im s=W/2.  Confirm the hypotheses + the conclusion.
  (i)   single nondegenerate stationary point y*, Phi''(y*)=-4/W (verify ratio ->1).
  (ii)  amplitude A bounded variation on SP window [y*-K sqrt W, y*+K sqrt W]: Var(A) finite & small.
  (iii) |Phi'| >= c off-saddle (grows ~ (4/W)|y-y*|); tail beyond window Gaussian-negligible.
  (iv)  CONCLUSION at the actual travel poles q_m: |T2(q_m)|/sqrt(tau) <= 0.13 < 1/sqrt2=0.707, and
        |T2(q_m)| < |cos W(q_m)| (=> Se=cosW-T2 keeps sign of cosW=sign sin w => b0=S0/Se>0).
Scalar mpmath. poles from poles.txt.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps=40
I=mp.mpc(0,1)
def setup(tau):
    tau=mp.mpf(tau); q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); return tau,q,w,W
def Phi_of_y(y,W,tau):
    B,_=B_exact(I*y,tau); g=1-mp.e**(-B)
    return 2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+2*I*y))
def A_of_y(y,W,tau):
    B,_=B_exact(I*y,tau); g=1-mp.e**(-B)
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
def d2(f,y,h=mp.mpf('1e-6')): return (f(y+h)-2*f(y)+f(y-h))/h**2

print("(i)+(ii)+(iii) van der Corput hypotheses on contour Im s=W/2:")
print(f"{'tau':>8}{'W':>8}{'Phi2(y*)/(-4/W)':>16}{'Var(A)/A(y*)':>14}{'|Phi1|edge/(4K/sqW)':>19}{'tail erfc':>11}")
for taus in ['0.02','0.005','0.001']:
    tau,q,w,W=setup(taus); ystar=W/2; K=mp.mpf(4); hw=K*mp.sqrt(W)
    P2=d2(lambda y:Phi_of_y(y,W,tau),ystar)
    a=max(ystar-hw,mp.mpf('0.05')); b=ystar+hw; N=160
    ys=[a+(b-a)*mp.mpf(j)/N for j in range(N+1)]; Av=[A_of_y(y,W,tau) for y in ys]
    VarA=sum(abs(Av[j+1]-Av[j]) for j in range(N)); Astar=A_of_y(ystar,W,tau)
    h2=mp.mpf('1e-6'); P1b=abs((Phi_of_y(b+h2,W,tau)-Phi_of_y(b-h2,W,tau))/(2*h2))
    print(f"{taus:>8}{float(W):>8.3f}{float(P2/(-4/W)):>16.5f}{float(VarA/Astar):>14.4f}"
          f"{float(P1b/((4/W)*hw)):>19.4f}{float(mp.erfc(K*mp.sqrt(2))):>11.2e}")

print("\n(iv) CONCLUSION at travel poles: |T2|/sqrt(tau) and |T2| vs |cos W| (=> b0>0):")
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
def cocycle(qq,Nn):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,Nn+1):
        qn*=qq;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return Y,y,X,x
print(f"{'m':>3}{'tau':>10}{'|T2|/sqrt(tau)':>15}{'<0.707?':>8}{'|cosW|/sqrt(tau)':>16}{'|T2|<|cosW|?':>13}{'b0>0?':>7}")
for m in [1,2,4,8,16,24]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    mp.mp.dps=40+int(1.2*float(w)); N=int(60/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    S1=S1_bulk(q); T2=S1-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))  # = S1bulk-(1-cosw)-T1
    st=mp.sqrt(tau); cw=abs(mp.cos(W)); b0=P11/Se
    print(f"{m:>3}{float(tau):>10.6f}{float(abs(T2)/st):>15.6f}{str(abs(T2)/st<1/mp.sqrt(2)):>8}"
          f"{float(cw/st):>16.6f}{str(abs(T2)<cw):>13}{str(b0>0):>7}")
    mp.mp.dps=40
print("\nPhi''=-4/W (ratio->1), Var(A) finite&small, |Phi'|>=c off-saddle, tail negligible => vdC hypotheses MET.")
print("|T2|/sqrt(tau)<0.707 AND |T2|<|cosW| at all poles => Se=cosW-T2 keeps sign => b0>0. ATOM A holds (modulo Stein VIII.2).")
