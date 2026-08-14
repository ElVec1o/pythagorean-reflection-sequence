"""
TYPESET (a): compute the EXPLICIT van der Corput bound constant for T2 (Atom A) and for the (a2) quantity,
so the lemmas state an actual number, not just "value < threshold".
van der Corput 2nd-deriv (Stein HA VIII Prop.2): |int_a^b A sin(Phi) dy| <= c2 * lam^{-1/2} * (|A(b)|+Var_[a,b]A),
  c2=8, lam=min|Phi''| on the window.  Plus the tail (|y-y*|>K sqrt(W)) bounded by the factorial/Gaussian decay.
Compute, on the window [y*-K sqrt W, y*+K sqrt W] (K=5):
  (1) lam=min|Phi''|; (2) |A(b)|+Var A; (3) vdC bound /sqrt(tau); compare to actual |T2|/sqrt(tau) and the
  Atom-A threshold |cosW|/sqrt(tau)~0.746.  ALSO the tail fraction (Gaussian).
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk
mp.mp.dps=30
I=mp.mpc(0,1)
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
def A_of_y(y,tau):
    B,_=B_exact(I*y,tau); g=1-mp.e**(-B)
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
def Phi_of_y(y,tau,W):
    B,_=B_exact(I*y,tau); g=1-mp.e**(-B)
    return 2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+2*I*y))
def Phi2(y,tau,W,h=mp.mpf('1e-5')):
    return (Phi_of_y(y+h,tau,W)-2*Phi_of_y(y,tau,W)+Phi_of_y(y-h,tau,W))/h**2
print("Explicit van der Corput bound for T2 (Atom A): bound = 8 lam^{-1/2}(|A(b)|+VarA), lam=min|Phi''| on window")
print(f"{'tau':>8}{'W':>8}{'lam=min|Phi2|':>14}{'|A|+VarA':>10}{'vdC/st':>9}{'|T2|/st':>9}{'thresh|cosW|/st':>15}{'<thresh?':>9}")
for taus in ['0.02','0.01','0.005','0.002','0.001']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau); ystar=W/2; K=mp.mpf(5); hw=K*mp.sqrt(W)
    a=max(ystar-hw,mp.mpf('0.5')); b=ystar+hw; N=300
    ys=[a+(b-a)*mp.mpf(j)/N for j in range(N+1)]
    Av=[A_of_y(y,tau) for y in ys]
    VarA=sum(abs(Av[j+1]-Av[j]) for j in range(N)); Ab=Av[-1]
    # min |Phi''| on a coarse subgrid
    lam=mp.mpf(10)
    for j in range(0,N+1,15):
        p2=abs(Phi2(ys[j],tau,W))
        if p2<lam: lam=p2
    vdc=8*lam**mp.mpf('-0.5')*(Ab+VarA)
    # actual T2 and threshold
    q=mp.e**(-tau); w=mp.sqrt(2/tau)
    T2=S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W)); thr=abs(mp.cos(W))
    print(f"{taus:>8}{float(W):>8.3f}{float(lam):>14.5f}{float(Ab+VarA):>10.5f}{float(vdc/st):>9.4f}{float(abs(T2)/st):>9.5f}{float(thr/st):>15.4f}{str(vdc<thr):>9}")
print("\nIf vdC/st is a fixed constant < |cosW|/st~0.746 for all tau: Atom-A bound EXPLICIT and rigorous (modulo Stein).")
print("(tail beyond window ~ erfc(K sqrt2)=%.1e negligible)" % float(mp.erfc(5*mp.sqrt(2))))
