#!/usr/bin/env python3
"""
THREE-PIECE van der Corput bound on the AP integrand I(y)=-A(y) sin Phi(y), s=iy.
T2 = int_0^{Y0} I(y) dy + Tail,   Tail handled by the convergent factorial sum.

Pieces of [0,Y0]:
 (S) saddle window  W_s = [y*-d, y*+d]:  Phi''~ -4/W, |Phi''|>=lambda_s; vdC-2 OR Gaussian.
 (L) left  [a, y*-d]:  Phi' >= m_L > 0  (Phi decreasing through y*, so Phi'>0 left of y*).
 (R) right [y*+d, Y0]: Phi' <= -m_R <0.
On (L),(R) use vdC FIRST-derivative (IBP):  |int A e^{iPhi}| <= (1/m)(2 sup A + Var A)... 
  actually |int_a^b A e^{iPhi}| <= (1/min|Phi'|)*(|A(b)|+|A(a)|+Var(A))  -- but cleaner:
  van der Corput 1st: |int A e^{iPhi}| <= C1/|Phi'|_min * (sup|A|+Var A). 
On (S) vdC 2nd: |int A e^{iPhi}| <= C2/sqrt(lambda_s) * (sup|A|+Var A), C2=8 (Stein).

GOAL: pick d (in units of sqrt(W) or W) so all three pieces are O(sqrt tau) with explicit C.
Phi'(y)~2 log(W/2y). Near y*: Phi'(y*+u)~ -4u/W (since Phi''=-4/W). So |Phi'|>=m means |u|>= mW/4.
Take d = beta*sqrt(W) (Gaussian half-width scale sqrt(W) since Phi''~1/W => width sqrt(W)).
Then at edge of window, |Phi'(y*+/-d)| ~ 4d/W = 4 beta/sqrt(W) = m_edge.
sqrt(lambda_s)=sqrt(4/W)=2/sqrt(W).
Let's MEASURE all pieces with d = beta*sqrt(W), several beta, and the amplitude integrals.
"""
import mpmath as mp
mp.mp.dps = 50
def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def B_series(s, tau, N=40):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpc(0)
    for n in range(1,N+1):
        p=2*n
        def Sf(a):
            c=mp.mpf(a)/2
            return 2**p*(mp.bernpoly(p+1,(s-1)+1+c)-mp.bernpoly(p+1,c))/(p+1)
        Q=Sf(2)+Sf(1)-((s-1)+1)
        tot+=f[n]*tau**(2*n)*Q
    return tot
def AP(y, W, tau):
    g=1-mp.e**(-B_series(mp.mpc(0,1)*y, tau))
    A=abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    Phi=2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
    return A,Phi
def amp(y,W,tau): return AP(y,W,tau)[0]
def integrand(y,W,tau):
    A,Phi=AP(y,W,tau); return -A*mp.sin(Phi)

print("Saddle window d=beta*sqrt(W). Measure: piece integrals (true), and vdC inputs.")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); ys=W/2; sW=mp.sqrt(W)
    beta=mp.mpf('3')           # window half-width in units of sqrt(W)
    d=beta*sW
    a=mp.mpf('0.5')
    Y0=ys+d
    yL=max(a, ys-d)
    # true piece integrals
    IS=mp.quad(lambda y: integrand(y,W,tau), [yL, ys, Y0])  # whole [yL,Y0] (window dominates)
    # tail of the SUM beyond Y0
    def phi(yy): return mp.log(mp.sinh(yy/2)/(yy/2))
    def Bint(n):
        s=mp.mpf(0); pt=phi(tau)
        for x in range(n): s+=phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
        return s
    # full T2 and the part from i> floor(Y0)
    T2=mp.mpf(0); Tail=mp.mpf(0)
    for i in range(1,int(W)+40):
        g=1-mp.e**(-Bint(i)); t=(-1)**i*W**(2*i)*g/mp.factorial(2*i)
        T2+=t
        if i>int(Y0): Tail+=t
    st=mp.sqrt(tau)
    print(f"\ntau={float(tau)}: W={float(W):.3f} y*={float(ys):.3f} sqrtW={float(sW):.3f} d={float(d):.3f} Y0={float(Y0):.2f}")
    print(f"  T2={mp.nstr(T2,8)} ({mp.nstr(T2/st,5)} sqrtT)  int[yL,Y0]={mp.nstr(IS,6)} ({mp.nstr(IS/st,5)} sqrtT)")
    print(f"  |Tail of sum i>Y0|={mp.nstr(abs(Tail),4)} ({mp.nstr(abs(Tail)/st,4)} sqrtT)  <- factorial-small")
    # amplitude over window
    supA=mp.mpf(0); VarA=mp.mpf(0); prev=None; N=200
    for k in range(N+1):
        y=yL+(Y0-yL)*mp.mpf(k)/N; av=amp(y,W,tau); supA=max(supA,av)
        if prev is not None: VarA+=abs(av-prev)
        prev=av
    lam_s=4/W
    print(f"  window: supA={mp.nstr(supA,5)} VarA={mp.nstr(VarA,5)}  lambda_s=4/W={mp.nstr(lam_s,5)} "
          f" vdC2 bound 8/sqrt(lam_s)*(supA+VarA)={mp.nstr(8/mp.sqrt(lam_s)*(supA+VarA),5)} ({mp.nstr(8/mp.sqrt(lam_s)*(supA+VarA)/st,5)} sqrtT)")
