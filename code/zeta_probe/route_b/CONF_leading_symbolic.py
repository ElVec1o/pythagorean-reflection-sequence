"""
LEADING-ORDER (closed form) of the state integral via the dominant Faddeev dilog.
As tau->0, the integral exponent is W(xi) = -xi^2/(4tau) + (1/(2tau)) [Li2(-a4 e^{ixi}) + Li2(-az e^{ixi})] + O(1),
with a4=q^4->1, az=2(1-q)q->2tau (SMALL).  The az dilog: Li2(-2tau e^{ixi}) ~ -2tau e^{ixi}+...,
so (1/2tau)Li2(-az e^{ixi}) ~ -e^{ixi} + O(tau) -- an O(1) term (goes into Phi_0, NOT the 1/tau exponent).
=> the 1/tau-order exponent is V(xi) = -xi^2/4 + (1/2) Li2(-e^{ixi}).   [a4->1]
Saddle:  V'(xi)= -xi/2 + (1/2)(d/dxi)Li2(-e^{ixi}) = -xi/2 - (i/2) log(1+e^{ixi}) = 0
   => xi* = -i log(1+e^{ixi*}).   This is the leading saddle (tau-independent!).
We solve it, evaluate V(xi*), V''(xi*), assemble the leading 2-saddle Gaussian, and check
the resulting constant in front of tau^{3/2} sin w equals (3/sqrt2)*? -> want overall 1/(4sqrt2).

The point of THIS script: show the LEADING constant is a CLOSED-FORM dilog expression
(no numerics-only fit), so the leading is genuinely proved-able; isolate exactly which
pieces remain numbers-only (the a1 correction).
"""
import mpmath as mp
mp.mp.dps = 50

# Leading saddle of V(xi) = -xi^2/4 + (1/2) Li2(-e^{i xi}),  V'(xi) = -xi/2 - (i/2) log(1+e^{i xi})
def Vp(xi):
    return -xi/2 - (1j/2)*mp.log(1 + mp.e**(1j*xi))
xstar = mp.findroot(Vp, mp.pi/2 - 1.0j, tol=mp.mpf(10)**-18, maxsteps=200)
print("leading saddle xi* (tau-indep) =", mp.nstr(xstar, 20))
# V'' = -1/2 - (i/2) d/dxi log(1+e^{ixi}) = -1/2 -(i/2)*(i e^{ixi}/(1+e^{ixi}))
e = mp.e**(1j*xstar)
Vpp = -mp.mpf(1)/2 + (mp.mpf(1)/2)*(e/(1+e))
V0 = -xstar**2/4 + mp.polylog(2, -e)/2
print("V(xi*)   =", mp.nstr(V0, 20))
print("V''(xi*) =", mp.nstr(Vpp, 20))
print("Re V0 =", mp.nstr(mp.re(V0),12), " (-> the 'volume' /(2tau); should give exp decay)")
print("Im V0 =", mp.nstr(mp.im(V0),12))
# Catalan-related? Im V0 vs Catalan G=0.915966; -pi^2/24=-0.4112
print("  cf pi^2/24 =", mp.nstr(mp.pi**2/24,10), "  Catalan=", mp.nstr(mp.catalan,10))

# Now: leading state-integral value.  INT ~ 2 Re[ e^{(1/tau) V0 + Phi0(xi*)} sqrt(2 pi /( -(1/tau)Vpp )) ]
# = 2 Re[ e^{V0/tau} e^{Phi0} sqrt(2 pi tau/(-Vpp)) ].   Phi0 = O(1) sub-exponential prefactor.
# The KEY: Re V0 < 0 gives exp(Re V0 / tau) decay; Im V0/tau is the rapid phase = where 'sin w' enters.
# Map to w: w=sqrt(2/tau).  Does Im(V0)/tau relate to w?  Im V0/tau vs w/?:
for tau in [mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.0025')]:
    w=mp.sqrt(2/tau)
    print(f"  tau={float(tau):.4f}: ImV0/tau={mp.nstr(mp.im(V0)/tau,12)}  w={mp.nstr(w,12)}  (ImV0/tau)/w={mp.nstr(mp.im(V0)/tau/w,8)}")
