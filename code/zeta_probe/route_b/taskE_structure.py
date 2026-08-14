#!/usr/bin/env python3
"""
Examine the structure of T2 = sum_{i>=1} (-1)^i psi(i),  psi(i) = W^{2i} g_i/(2i)!.

KEY for van der Corput: treat the alternating sum as an oscillatory integral.
Use the standard 'alternating sum -> integral' device WITHOUT the divergent AP form:
   sum_{i>=1} (-1)^i a_i  where a_i = psi(i).
We want a SECOND-DERIVATIVE (van der Corput) bound.

We examine psi(i) as a smooth real function PSI(y)=W^{2y} g_y/Gamma(2y+1):
 - its peak location and width (the 'Poisson/Bessel' peak at y ~ W/2),
 - the magnitude at the peak ~ relevant to amplitude,
 - g_y = 1-e^{-B_y} ~ B_y small near saddle.

Then we note: sum_{i}(-1)^i PSI(i) = sum_i e^{i pi i} PSI(i) is an exponential sum with
frequency 1/2 (period 2). By Poisson summation,
   sum_i (-1)^i PSI(i) = sum_m (-1)^? \hat{PSI}(m+1/2) ...
Actually cleaner: sum_{i in Z}(-1)^i f(i) = sum_{m in Z} \hat f(m+1/2)  where \hat f(xi)=int f(y)e^{-2pi i xi y}dy.
The dominant terms are m=0,-1 i.e. xi=+/-1/2: \hat{PSI}(+/-1/2) = int PSI(y) e^{-/+ pi i y} dy.
THAT integral converges (PSI decays factorially) and has a stationary phase!  The phase of
PSI(y) e^{-pi i y}: PSI ~ e^{2y log W - logGamma(2y+1)} so d/dy[2y log W - logGamma(2y+1) - pi y]...
Wait PSI is real; the oscillation comes from e^{-pi i y}. Let's just compute |int PSI(y)e^{i pi y}dy|.
"""
import mpmath as mp
mp.mp.dps = 60

def phi(y): return mp.log(mp.sinh(y/2)/(y/2))
def Bint(n, tau):  # integer
    s=mp.mpf(0); pt=phi(tau)
    for x in range(n): s += phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
    return s

tau=mp.mpf('0.01'); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
print(f"tau={float(tau)}, w={float(w):.4f}, W={float(W):.4f}, y*=W/2={float(W/2):.4f}")

# PSI(i) at integers: peak location & width
print("\ni, psi(i)=W^2i g_i/(2i)!, |psi|:")
peak=mp.mpf(0); ipeak=0
vals=[]
for i in range(1, int(W)+30):
    g=1-mp.e**(-Bint(i,tau))
    p=W**(2*i)*g/mp.factorial(2*i)
    vals.append((i,p,g))
    if abs(p)>peak: peak=abs(p); ipeak=i
print(f"peak |psi(i)| at i={ipeak} (W/2={float(W/2):.2f}, W={float(W):.2f}), value={mp.nstr(peak,8)}")
# the UNMODULATED Poisson/Bessel peak: W^{2i}/(2i)! peaks where? ratio test: W^2/((2i+1)(2i+2))=1 => i~W/2
for i in [ipeak-3,ipeak,ipeak+3, int(W)-2, int(W)]:
    if 1<=i<len(vals)+1:
        ii,p,g=vals[i-1]
        rawpeak=W**(2*ii)/mp.factorial(2*ii)
        print(f"  i={ii}: psi={mp.nstr(p,6)}, g_i={mp.nstr(g,6)}, raw W^2i/(2i)!={mp.nstr(rawpeak,6)}")

# Poisson dominant Fourier coefficient: F(xi)=int_0^inf PSI(y) e^{-2pi i xi y} dy at xi=1/2
def PSI(y):
    # need g_y at real non-integer y -> use B at complex? B_y for real y via the loggamma cont.
    # but here just integer-grid Poisson check; do the integral with B continued.
    pass
print("\nThe key claim to verify next: |sum (-1)^i psi(i)| <= |F(1/2)|+|F(-1/2)|+tail,")
print("and F(1/2)=int PSI(y)e^{-pi i y}dy is an oscillatory integral with stationary phase.")
print("raw alternating sum of W^2i/(2i)! (g=1) = cos W - 1 =", mp.nstr(mp.cos(W)-1,8),
      " (this is the 1-cos w part already removed; with g it's T2).")
