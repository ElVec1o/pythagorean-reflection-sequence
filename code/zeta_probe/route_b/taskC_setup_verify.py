#!/usr/bin/env python3
"""
TASK C - step 0: verify the exact construction of B_s, g_s, psi(iy), and that
the Abel-Plana representation T2 = -int_0^inf Im(psi(iy))/sinh(pi y) dy
reproduces the TRUE T2 = S1 - (1-cos w) - (cos w - cos W).

phi(y) = log(sinh(y/2)/(y/2)) = sum_{k>=1} log(1+(y/(2 pi k))^2)   [product formula, exact]
b(x)   = phi((2x+2)tau) + phi((2x+1)tau) - phi(tau)
B_s    = sum_{i'=0}^{s-1} b(i')   (for integer s; analytic continuation needed for complex s)

For the Abel-Plana integral we need B at COMPLEX argument s = iy. The integer-sum form
B_s = sum_{i'=0}^{s-1} b(i') must be analytically continued. We use the EXACT antidifference:
B_s = Phi_cum(s) where the continuation is built from the Hurwitz-zeta-style antidifference of
phi-evaluated-at-arithmetic-progressions. We instead use the directly-convergent product/series
representation of B_s as an analytic function of s (the phi-product over k with closed-form
antidifference in s of log(1+((2 i' +c) tau/(2 pi k))^2)).

Antidifference of log(1 + ((a*m + r)/L)^2) over m=0..s-1:
   sum_{m=0}^{s-1} log(1 + ((a m + r)/L)^2)
 = sum log( (a m + r + i L)(a m + r - i L) ) - 2 s log L
 = [logGamma-type]:  using sum_{m=0}^{s-1} log(m + z) = logGamma(s+z) - logGamma(z),
   with z = (r +/- i L)/a, and prefactor:  a m + r +/- iL = a (m + (r +/- iL)/a).
   => sum_{m=0}^{s-1} log(a m + r +/- iL) = s log a + logGamma(s + (r +/- iL)/a) - logGamma((r +/- iL)/a)
This is analytic in s (complex). This gives B_s for ANY complex s, exactly, via mpmath loggamma.
"""
import mpmath as mp
mp.mp.dps = 60

def phi_real(y):
    # phi(y) = log( sinh(y/2)/(y/2) ); robust near 0
    if abs(y) < mp.mpf('1e-20'):
        return (y*y)/24  # leading term
    return mp.log(mp.sinh(y/2)/(y/2))

# --- B_s as analytic function of complex s, via loggamma antidifference ---
# b(x) = phi((2x+2)tau) + phi((2x+1)tau) - phi(tau)
# phi(c) over product: phi(c) = sum_{k>=1} log(1 + (c/(2 pi k))^2)
# So B_s = sum_{x=0}^{s-1} [ sum_k log(1+((2x+2)tau/(2pi k))^2) + log(1+((2x+1)tau/(2pi k))^2) ] - s*phi(tau)
# term1: a=2tau, r=2tau ; term2: a=2tau, r=tau ; L = 2 pi k.
def antidiff_logfactor(s, a, r, L):
    # sum_{m=0}^{s-1} log(1 + ((a m + r)/L)^2)
    #   = sum log(a m + r + iL) + log(a m + r - iL) - 2 s log L
    zp = (r + 1j*L)/a
    zm = (r - 1j*L)/a
    zp = mp.mpc(zp); zm = mp.mpc(zm)
    sp = s*mp.log(a) + mp.loggamma(s + zp) - mp.loggamma(zp)
    sm = s*mp.log(a) + mp.loggamma(s + zm) - mp.loggamma(zm)
    return sp + sm - 2*s*mp.log(L)

def B_s(s, tau, Kmax=400):
    s = mp.mpc(s)
    a = 2*tau
    tot = mp.mpc(0)
    # sum over k of [antidiff for r=2tau] + [antidiff for r=tau]
    for k in range(1, Kmax+1):
        L = 2*mp.pi*k
        tot += antidiff_logfactor(s, a, 2*tau, L)
        tot += antidiff_logfactor(s, a, 1*tau, L)
    tot += -s*phi_real(tau)
    return tot

# sanity: compare B_s for INTEGER s against direct sum of b(x)
def B_int_direct(S, tau, Kmax=400):
    def phi_prod(c):
        tot = mp.mpf(0)
        for k in range(1, Kmax+1):
            tot += mp.log(1 + (c/(2*mp.pi*k))**2)
        return tot
    tot = mp.mpf(0)
    for x in range(S):
        tot += phi_prod((2*x+2)*tau) + phi_prod((2*x+1)*tau) - phi_real(tau)
    return tot

tau = mp.mpf('0.01')
print("== Check B_s analytic continuation vs direct integer sum (Kmax=400) ==")
for S in [1,2,3,5,8]:
    a1 = B_s(S, tau)
    a2 = B_int_direct(S, tau)
    print(f"  s={S}:  B_s(cont)={mp.nstr(mp.re(a1),12)}  direct={mp.nstr(a2,12)}  |im|={mp.nstr(abs(mp.im(a1)),3)}  diff={mp.nstr(abs(a1-a2),3)}")

# Also compare against phi exact (not truncated product) for phi_real to gauge Kmax error
print("\n== phi product truncation check (Kmax) ==")
for c in [tau, 2*tau, 14*tau, 60*tau]:
    exact = phi_real(c)
    for Kmax in [100,400,2000]:
        approx = sum(mp.log(1+(c/(2*mp.pi*k))**2) for k in range(1,Kmax+1))
        print(f"  c={mp.nstr(c,4)} Kmax={Kmax}: err={mp.nstr(abs(exact-approx),3)}")
