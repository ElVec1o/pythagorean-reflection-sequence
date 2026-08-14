#!/usr/bin/env python3
"""
ADVERSARIAL CHECK 2 (independent): the TAIL-REPAIR category error and pole behaviour.

The colleague's repair (gap #2): the tail of the real-axis integral, y > Y0 = y*+K sqrt(W),
is "controlled separately by the factorial decay of a_i = W^{2i}/(2i)!" with erfc(K sqrt2) decay.

CLAIM TO TEST: the tail of the INTEGRAL  int_{Y0}^{pole} (-Im psi(iy)/sinh(pi y)) dy
is NOT the same object as the tail of the SERIES  sum_{i>I0} (-1)^i a_i g_i.
Abel-Plana equates the FULL sum to the FULL integral, not head-to-head / tail-to-tail.

We compute, at a modest tau where the pole pi/tau is reachable:
  (1) series tail   ST(I0) = sum_{i>I0} (-1)^i a_i g_i        (a_i,g_i at INTEGER i)
  (2) abs series tail sum_{i>I0} a_i |g_i|  (the bound the colleague invokes)
  (3) integral tail IT(Y0) = int_{Y0}^{Ymax} integrand dy     (Y0 = I0, Ymax -> pole)
  (4) integral head = int_0^{Y0} integrand dy
and check head+tail = T2_direct, and whether ST(I0) ~ IT(Y0) (they should NOT match).

Also: integrand magnitude as y -> pole, to decide if the integral even converges.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 45
I = mp.mpc(0, 1)

def setup(tau):
    tau = mp.mpf(tau); q = mp.e**(-tau); w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2)
    return tau, q, w, W

def T2_direct(tau):
    tau, q, w, W = setup(tau)
    return S1_bulk(q) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def psi_iy(y, W, tau):
    s = I*y
    B,_ = B_exact(s, tau); g = 1-mp.e**(-B)
    return mp.e**(2*s*mp.log(W)) * g / mp.gamma(2*s+1)

def integrand(y, W, tau):
    if y == 0: return mp.mpf(0)
    return -mp.im(psi_iy(y, W, tau))/mp.sinh(mp.pi*y)

def a_i(i, W):
    return W**(2*i)/mp.factorial(2*i)
def g_i_int(i, tau):
    B,_ = B_exact(mp.mpc(i), tau)
    return 1 - mp.e**(-mp.re(B))

tau = mp.mpf('0.2')
tau,q,w,W = setup(tau)
ystar = W/2; pole = mp.pi/tau
print(f"tau={float(tau)}  W={float(W):.4f}  ystar={float(ystar):.4f}  pole pi/tau={float(pole):.4f}")
T2d = T2_direct(tau)
print(f"T2_direct = {mp.nstr(T2d,14)}")

# series: sum_{i>=1} (-1)^i a_i g_i   (should equal T2)
Imax = 80
terms = []
for i in range(1, Imax+1):
    terms.append(((-1)**i) * a_i(i,W) * g_i_int(i,tau))
S = mp.fsum(terms)
print(f"series sum (i=1..{Imax}) = {mp.nstr(S,14)}   |series-direct|={mp.nstr(abs(S-T2d),4)}")

# pick I0 = round(ystar) + a few sigma; window K sqrt(W)
K = mp.mpf(4)
I0 = int(mp.floor(ystar + K*mp.sqrt(W)))
print(f"\nWindow edge / split index  I0 = floor(ystar + K sqrt(W)) = {I0}  (K={int(K)})")

# (1) series tail beyond I0
ST = mp.fsum(terms[I0:])          # i = I0+1 .. Imax
ST_abs = mp.fsum([abs(t) for t in terms[I0:]])
print(f"(1) SERIES tail  sum_{{i>{I0}}} (-1)^i a_i g_i        = {mp.nstr(ST,8)}")
print(f"(2) ABS series tail sum_{{i>{I0}}} a_i|g_i|          = {mp.nstr(ST_abs,8)}   <-- colleague's bound object")

# (3) integral tail from Y0=I0 up to near pole
Y0 = mp.mpf(I0)
Ymax = pole*mp.mpf('0.985')
f = lambda y: integrand(y, W, tau)
IT = mp.quad(f, [Y0, (Y0+Ymax)/2, Ymax])
# integral head
IH = mp.quad(f, [mp.mpf(0), ystar/2, ystar, ystar*mp.mpf('1.5'), Y0])
print(f"(3) INTEGRAL tail int_{{{int(Y0)}}}^{{{float(Ymax):.2f}}} integrand dy  = {mp.nstr(IT,8)}")
print(f"(4) INTEGRAL head int_0^{{{int(Y0)}}} integrand dy            = {mp.nstr(IH,8)}")
print(f"    head+tail = {mp.nstr(IH+IT,10)}   |vs direct|={mp.nstr(abs(IH+IT-T2d),4)}")
print(f"\n   COMPARE series-tail (1)={mp.nstr(ST,6)}  vs  integral-tail (3)={mp.nstr(IT,6)}")
print(f"   |series_tail - integral_tail| = {mp.nstr(abs(ST-IT),5)}   (if large => head/tail not interchangeable)")
print(f"   sqrt(tau) = {mp.nstr(mp.sqrt(tau),5)};  is integral-tail = O(sqrt tau)? ratio IT/sqrt(tau)={mp.nstr(IT/mp.sqrt(tau),5)}")

# pole behaviour of |integrand| and of A(y)
print("\n--- integrand magnitude approaching the pole y=pi/tau ---")
print(f"   {'y/pole':>8} {'Re B(iy)':>14} {'A=|g|sqrt(coth/piy)':>22} {'|integrand|':>16}")
for frac in [mp.mpf('0.7'),mp.mpf('0.9'),mp.mpf('0.97'),mp.mpf('0.99'),mp.mpf('0.997'),mp.mpf('0.999')]:
    y = pole*frac
    B,_ = B_exact(I*y, tau); g = 1-mp.e**(-B)
    A = abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    ig = abs(integrand(y,W,tau))
    print(f"   {float(frac):>8.3f} {mp.nstr(mp.re(B),7):>14} {mp.nstr(A,7):>22} {mp.nstr(ig,7):>16}")
