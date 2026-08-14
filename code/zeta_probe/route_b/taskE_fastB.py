#!/usr/bin/env python3
"""
Fast B at real y via product-formula phi antidifference is O(y) per point and exact at
integers; for the CONTINUOUS integral we need B at non-integer y. Use the tau-series
   B_s = sum_{n>=1} f_n tau^{2n} Q_n(s-1),  f_n=[y^{2n}]phi,  Q_n Faulhaber.
valid for |s|<pi/tau. Near the saddle y* and up to Y0~ a few*y*, this converges fast.
We build f_n and Q_n once.
"""
import mpmath as mp
mp.mp.dps = 50

# phi(y)=log(sinh(y/2)/(y/2)) = sum_{n>=1} f_n y^{2n}.  Get f_n from the Taylor series.
def phi_coeffs(N):
    # phi(y) = sum_{k>=1} log(1+(y/(2 pi k))^2) = -sum_{n>=1} (-1)^n/n * (1/(2pi)^{2n}) zeta(2n) y^{2n}
    # check: log(1+u)=sum_{m>=1} (-1)^{m+1} u^m/m, u=(y/(2pi k))^2
    #  => coeff of y^{2n}: sum_k (-1)^{n+1}/n * (1/(2 pi k)^{2n}) = (-1)^{n+1}/n * zeta(2n)/(2pi)^{2n}
    f=[mp.mpf(0)]  # f[0] unused
    for n in range(1,N+1):
        fn = (-1)**(n+1)/mp.mpf(n) * mp.zeta(2*n)/(2*mp.pi)**(2*n)
        f.append(fn)
    return f

# Q_n(m) = sum_{i=0}^m [(2i+2)^{2n}+(2i+1)^{2n}-1]   (Faulhaber, degree 2n+1 in m); we just sum.
def Qn(n, m):
    # m can be complex (m = s-1); use the Faulhaber polynomial via Bernoulli? For verification
    # we only need integer/real m up to Y0; sum directly when m is a nonneg integer-ish.
    # For real continuous m we need the polynomial. Build via sympy-free: use mp.bernpoly.
    # sum_{i=0}^m (2i+a)^{2n} : let j range; use the Hurwitz/Bernoulli closed form:
    #   sum_{i=0}^{m} (2i+a)^{p} = 2^p sum_{i=0}^m (i+a/2)^p
    #   sum_{i=0}^m (i+c)^p = (B_{p+1}(m+1+c)-B_{p+1}(c))/(p+1)   [Bernoulli polynomial]
    p=2*n
    def S(a):
        c=mp.mpf(a)/2
        return 2**p*(mp.bernpoly(p+1, m+1+c)-mp.bernpoly(p+1, c))/(p+1)
    # sum_{i=0}^m 1 = m+1
    return S(2)+S(1)-(m+1)

def B_series(s, tau, N=40):
    s=mp.mpf(s) if not isinstance(s,mp.mpc) else s
    f=phi_coeffs(N)
    tot=mp.mpf(0) if not isinstance(s,mp.mpc) else mp.mpc(0)
    for n in range(1,N+1):
        tot += f[n]*tau**(2*n)*Qn(n, s-1)
    return tot

# Validate against exact integer B (product form)
def phi(y): return mp.log(mp.sinh(y/2)/(y/2))
def Bint(n, tau):
    s=mp.mpf(0); pt=phi(tau)
    for x in range(n): s+=phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
    return s

print("Validate B_series (tau-series, Faulhaber) vs exact integer B (product form):")
for tau in [mp.mpf('0.1'),mp.mpf('0.05'),mp.mpf('0.01')]:
    print(f" tau={float(tau)}:")
    for n in [1,3,5,8]:
        bs=B_series(n,tau); bi=Bint(n,tau)
        print(f"   n={n}: B_series={mp.nstr(bs,12)}  B_int={mp.nstr(bi,12)}  diff={mp.nstr(abs(bs-bi),3)}")
# at the saddle (real y*) check convergence
tau=mp.mpf('0.01'); W=mp.sqrt(2/tau)*mp.e**(-tau/2)
print(f"\nAt saddle y*=W/2={float(W/2):.3f} (tau=0.01): B_series(y*)={mp.nstr(B_series(W/2,tau),10)}")
print(f"pi/tau (series radius) = {float(mp.pi/tau):.1f}, so series valid up to y<{float(mp.pi/tau):.0f}")
