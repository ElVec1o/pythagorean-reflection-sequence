#!/usr/bin/env python3
"""
Set up van der Corput on  J = int_0^inf PSI(y) e^{i pi y} dy,  PSI(y)=g_y e^{Psi(y)},
   Psi(y) = 2y log W - log Gamma(2y+1)   (REAL, concave, Bessel/Poisson peak),
   g_y = 1-e^{-B_y} in [0,1), slowly varying.

The integrand = g_y exp( Psi(y) + i pi y ).  This is NOT a pure phase oscillation: Psi is a
REAL exponent (sharp peak), pi y is the oscillation. The honest van der Corput object is the
COMPLEX-phase integral: complete the exponent  Theta(y) = -i Psi(y) + pi y  is not right either.

Correct framing (stationary phase for a peaked amplitude times oscillation):
  J = int g_y e^{Psi(y)} e^{i pi y} dy.
Let M(y) = g_y e^{Psi(y)} >= 0  (the peaked amplitude, max at y_p ~ W/2).
Then J = int M(y) e^{i pi y} dy. Phase = pi y is LINEAR => integrate by parts using M:
  |J| <= (1/pi) Var(M) = (1/pi) * 2 * max M = (2/pi) max M   [since M is unimodal, Var=2 max M].
THIS is the clean van der Corput / first-derivative (stationary phase has Phi'=pi != 0 everywhere!)
=> NO stationary point on the real axis; pure IBP gives |J| <= (2/pi) sup M.
But sup M ~ peak of g_y e^{Psi} which is O(?) -- check if that already gives sqrt(tau).

Actually the SECOND-derivative test enters because M itself is e^{(concave)}: the width of M is
~ sqrt(W), and IBP once gives (1/pi)Var(M). Let's just MEASURE sup M and Var(M).
"""
import mpmath as mp
mp.mp.dps = 50

def phi_coeffs(N):
    f=[mp.mpf(0)]
    for n in range(1,N+1):
        f.append((-1)**(n+1)/mp.mpf(n)*mp.zeta(2*n)/(2*mp.pi)**(2*n))
    return f
_F={}
def B_series(y, tau, N=40):
    if N not in _F: _F[N]=phi_coeffs(N)
    f=_F[N]; tot=mp.mpf(0)
    for n in range(1,N+1):
        p=2*n
        def S(a):
            c=mp.mpf(a)/2
            return 2**p*(mp.bernpoly(p+1,(y-1)+1+c)-mp.bernpoly(p+1,c))/(p+1)
        Q=S(2)+S(1)-((y-1)+1)
        tot+=f[n]*tau**(2*n)*Q
    return tot

def M(y, W, tau):
    if y<=0: return mp.mpf(0)
    B=B_series(y,tau); g=1-mp.e**(-B)
    Psi=2*y*mp.log(W)-mp.loggamma(2*y+1)
    return g*mp.e**(Psi)

print("M(y)=g_y e^{Psi(y)} = |PSI(y)|. sup M, Var(M)=2 sup M (unimodal), bound |J|<=(2/pi)supM.")
print(f"{'tau':>9} {'y_peak':>8} {'supM':>14} {'supM/sqrtT':>11} {'(2/pi)supM/sqrtT':>16} {'|J|/sqrtT(true)':>16}")
for tau in [mp.mpf(x) for x in ['0.1','0.05','0.02','0.01','0.005']]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    # find peak of M near W/2
    yp=mp.findmax(lambda y: M(y,W,tau), float(W/2)) if False else None
    # simple scan for peak
    best=mp.mpf(0); yb=W/2
    yy=mp.mpf(1)
    while yy<W:
        v=M(yy,W,tau)
        if v>best: best=v; yb=yy
        yy+=mp.mpf('0.25')
    # refine
    for dy in [mp.mpf('0.1'),mp.mpf('0.02'),mp.mpf('0.004')]:
        yy=yb-5*dy
        while yy<=yb+5*dy:
            v=M(yy,W,tau)
            if v>best: best=v; yb=yy
            yy+=dy
    st=mp.sqrt(tau)
    bound=(2/mp.pi)*best
    print(f"{float(tau):>9} {float(yb):>8.3f} {mp.nstr(best,7):>14} {mp.nstr(best/st,6):>11} "
          f"{mp.nstr(bound/st,6):>16} {'~0.02-0.024':>16}")
