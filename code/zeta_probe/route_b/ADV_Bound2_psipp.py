"""
BOUND 2: the g-phase second derivative Psi''(y) = d^2/dy^2 arg(1 - e^{-B_{iy}}) is o(1/W),
so Phi'' = Phi0'' + Psi'' = -4/W + o(1/W) stays nondegenerate for van der Corput hyp (a).
Claim (analytic, from the exact tau-series): on the SP window |y-W/2|<=1.5 sqrt(W),
  B_{iy} ~ sqrt(tau),  B'_{iy} ~ tau,  B''_{iy} ~ tau^{3/2},  |g_{iy}|=|1-e^{-B}| >= c sqrt(tau) (>0),
  => |Psi''| = O(tau) = o(1/W)  [since 1/W ~ sqrt(tau/2)].  Hence Psi''*W -> 0.
Verify all numerically with the EXACT tau-series B(s)=sum phi_n tau^{2n}(P_n(2s)-s).
Scalar mpmath, dps 40, memory-safe.
"""
import mpmath as mp
mp.mp.dps = 40
I = mp.mpc(0,1)

def phi_n(n): return (-1)**(n+1)*mp.zeta(2*n)/(n*(2*mp.pi)**(2*n))
def Pn_2s(n, s): return (mp.bernpoly(2*n+1, 2*s+1)-mp.bernpoly(2*n+1,1))/(2*n+1)
def Bser(s, tau, N=36): return mp.fsum(phi_n(n)*tau**(2*n)*(Pn_2s(n,s)-s) for n in range(1,N+1))

def B_iy(y, tau): return Bser(I*y, tau)          # analytic in y (complex-valued)
def logg(y, tau): return mp.log(1 - mp.e**(-B_iy(y, tau)))   # log g_{iy}, analytic near window

print(f"{'tau':>8} {'W':>9} {'1/W~sqrtt/2':>12} {'max|B|/sqrtt':>12} {'max|Bp|/tau':>12} "
      f"{'max|Bpp|/t^1.5':>14} {'min|g|/sqrtt':>12} {'max|Psipp|':>12} {'max|Psipp|*W':>13} {'max|Psipp|/tau':>14}")
for taus in ['0.05','0.02','0.01','0.005','0.002']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau); y0 = W/2; R = mp.mpf('1.5')*mp.sqrt(W)
    ys = [y0 + R*mp.mpf(k)/8 for k in range(-8,9)]
    Bmax=Bpmax=Bppmax=mpsi=mpsiW=mpsit=mp.mpf(0); gmin=mp.inf
    for y in ys:
        B = B_iy(y, tau)
        Bp = mp.diff(lambda t: B_iy(t,tau), y)         # B'_{iy}
        Bpp = mp.diff(lambda t: B_iy(t,tau), y, 2)     # B''_{iy}
        g = 1 - mp.e**(-B)
        Fpp = mp.diff(lambda t: logg(t,tau), y, 2)     # (log g)''
        psipp = mp.im(Fpp)                             # Psi'' = Im (log g)''
        Bmax=max(Bmax,abs(B)); Bpmax=max(Bpmax,abs(Bp)); Bppmax=max(Bppmax,abs(Bpp))
        gmin=min(gmin,abs(g)); mpsi=max(mpsi,abs(psipp)); mpsiW=max(mpsiW,abs(psipp)*W); mpsit=max(mpsit,abs(psipp)/tau)
    st=mp.sqrt(tau)
    print(f"{taus:>8} {float(W):>9.4f} {float(1/W):>12.5f} {float(Bmax/st):>12.5f} {float(Bpmax/tau):>12.5f} "
          f"{float(Bppmax/tau**mp.mpf('1.5')):>14.4f} {float(gmin/st):>12.5f} {float(mpsi):>12.3e} {float(mpsiW):>13.4f} {float(mpsit):>14.5f}")
print("\nNeed: |B|/sqrtt, |Bp|/tau, |Bpp|/t^1.5, |g|/sqrtt all BOUNDED (scalings hold);")
print("      |Psipp|*W -> 0 (so Psi''=o(1/W)); |Psipp|/tau bounded (Psi''=O(tau)).")
print("Then Phi''=-4/W + Psi'' = -4/W(1+o(1)), nondegenerate => vdC hyp (a) RIGOROUS.")
