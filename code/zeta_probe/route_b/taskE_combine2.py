#!/usr/bin/env python3
"""
FAST combined vdC bound. Use ANALYTIC leading phase derivatives:
  Phi(y) = 2y log W + arg g_{iy} - Im logGamma(1+2iy).
  Phi'(y) = 2 log W + (d/dy arg g) - 2 Re psi0(1+2iy)   [psi0=digamma; since Im logGamma'(1+2iy)*... 
     d/dy Im logGamma(1+2iy) = Im[2i psi0(1+2iy)] = 2 Re psi0(1+2iy)].
  Also d/dy 2y log W = 2 log W. So Phi'(y)=2 log W - 2 Re psi0(1+2iy) + (arg g)'.
  Note 2 Re psi0(1+2iy) ~ 2 log(2y) for large y, so Phi' ~ 2 log(W/(2y)). 
  Phi''(y) = -2 d/dy Re psi0(1+2iy) + (arg g)'' = -2 Re[2i psi1(1+2iy)] + ...
           = 4 Im psi1(1+2iy) + (arg g)''.   [psi1=trigamma]
The (arg g) terms are small (g~B small near saddle); we include them via cheap FD only where needed,
but for the LOWER bound on |Phi''| and |Phi'| the analytic Bessel part dominates. We compute the
analytic part exactly (digamma/trigamma, fast) and add a measured small correction.
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
def amp(y,W,tau):
    g=1-mp.e**(-B_series(mp.mpc(0,1)*y,tau))
    return abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
def Phi1_analytic(y,W):  # leading Phi' ignoring (arg g)'  (Bessel part, exact)
    s=mp.mpc(0,1)*y
    return 2*mp.log(W) - 2*mp.re(mp.digamma(1+2*s))
def Phi2_analytic(y):    # leading Phi'' = 4 Im psi1(1+2iy), exact
    s=mp.mpc(0,1)*y
    return 4*mp.im(mp.polygamma(1,1+2*s))

# sanity: compare analytic Phi' to FD-on-full-Phi at a couple points
tau=mp.mpf('0.01'); W=mp.sqrt(2/tau)*mp.e**(-tau/2); ys=W/2
def fullPhi(y):
    g=1-mp.e**(-B_series(mp.mpc(0,1)*y,tau))
    return 2*y*mp.log(W)+mp.arg(g)-mp.im(mp.loggamma(1+mp.mpc(0,1)*2*y))
h=mp.mpf('1e-6')
for y in [ys*mp.mpf('0.5'), ys, ys*mp.mpf('1.5'), ys*mp.mpf('3')]:
    fd1=(fullPhi(y+h)-fullPhi(y-h))/(2*h)
    fd2=(fullPhi(y+h)-2*fullPhi(y)+fullPhi(y-h))/h**2
    print(f" y={float(y):7.3f}: Phi' FD={mp.nstr(fd1,6)} analytic={mp.nstr(Phi1_analytic(y,W),6)} "
          f"|| Phi'' FD={mp.nstr(fd2,6)} analytic={mp.nstr(Phi2_analytic(y),6)}")
print("(analytic = Bessel part; the (arg g)' correction is the small gap)")
