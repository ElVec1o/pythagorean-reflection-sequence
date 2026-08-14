#!/usr/bin/env python3
"""
Pin down the FACTORIAL TAIL bound rigorously and check window choice Y0.
Tail = sum_{i>Y0}(-1)^i psi(i),  |Tail| <= sum_{i>Y0} psi(i) <= sum_{i>Y0} W^{2i}/(2i)!  (since g_i<1).
For i >= I0 with I0 >= e W /... use ratio psi(i+1)/psi(i) ~ W^2/((2i+1)(2i+2)).
For 2i+2 > e W (i.e. i > eW/2 -1), terms decay geometrically with ratio < 1/e? Let's get explicit.
The tail of sum_{i>Y0} W^{2i}/(2i)!:  for i0 with (2 i0)(2 i0) > W^2 e^2... 
Standard: sum_{i> i0} x^i/i! <= x^{i0+1}/( (i0+1)! (1 - x/(i0+2)) ) for x<i0+2.
Here with W^{2i}/(2i)! = (W^2)^i/(2i)!: bound tail by a geometric series once 2i>W e.
We just COMPUTE the exact tail with high precision and compare to sqrt(tau), for Y0=c*W.
"""
import mpmath as mp
mp.mp.dps = 120
def phi(yy): return mp.log(mp.sinh(yy/2)/(yy/2))
def Bint(n, tau):
    s=mp.mpf(0); pt=phi(tau)
    for x in range(n): s+=phi((2*x+2)*tau)+phi((2*x+1)*tau)-pt
    return s

print("Exact factorial tail |sum_{i>Y0} psi(i)| for Y0 = c*W, c in {1.0,1.3,1.6,2.0}. dps=120.")
for tau in [mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005'),mp.mpf('0.002')]:
    w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); st=mp.sqrt(tau)
    line=f"tau={float(tau):<7} W={float(W):7.3f}: "
    for c in [1.0,1.3,1.6,2.0]:
        Y0=c*W
        tail=mp.mpf(0); tailabs=mp.mpf(0)
        for i in range(int(Y0)+1, int(2.5*W)+60):
            g=1-mp.e**(-Bint(i,tau))
            psi=W**(2*i)*g/mp.factorial(2*i)
            tail+=(-1)**i*psi; tailabs+=psi
        line+=f" c={c}:|tail|={mp.nstr(tailabs/st,3)}sT"
    print(line)
