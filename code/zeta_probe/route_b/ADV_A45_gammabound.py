"""
Explicit lower bounds for |Gamma| used in the A4/A5 constant, checked numerically.

(B1) On the TOP side, argument z = (2 sigma+1) + i W, x=2 sigma+1 >= 2, y=W.
We use the EXACT product
    |Gamma(x+iy)|^2 = |Gamma(x)|^2 * prod_{n>=0} (1 + y^2/(x+n)^2)^{-1}.
A clean closed lower bound: for x>=1,
    |Gamma(x+iy)| >= |Gamma(x)| * |Gamma(1+iy)|/Gamma(1) ... (NO; instead use the standard)
Standard inequality (DLMF 5.6.7 region / Stirling): for x>=1/2,
    |Gamma(x+iy)| >= sqrt(2pi) |y|^{x-1/2} e^{-pi|y|/2} * exp(-1/(6|y|))   ... we TEST this.
We test the *combination* that appears, namely
    W^{2 sigma}/|Gamma(2 sigma+1+iW)| * e^{-pi W/2}^{-1}  i.e. the cancellation,
by checking  R(sigma):= W^{2sigma} e^{pi W/2} / |Gamma(2 sigma+1+iW)|  and that it has the
sqrt-tau scaling claimed (peak ~ const, area ~ sqrt(tau)*const).
"""
import mpmath as mp
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)

# Stirling-based explicit lower bound candidate for |Gamma(x+iy)|, y>0, x>=1/2:
#   |Gamma(x+iy)| >= sqrt(2 pi) (x^2+y^2)^{(x-1/2)/2} exp(-x - y*atan(y/x)) * exp(-1/(6 sqrt(x^2+y^2)))
# from log|Gamma(z)| = (x-1/2)log|z| - Re z - y*arg? Let's just test |z|^{x-1/2} e^{-x} e^{-y arctan(y/x)} sqrt(2pi).
def gamma_lower_stirling(x,y):
    z=mp.mpf(x)+1j*mp.mpf(y); r=abs(z); th=mp.atan2(y,x)
    # |Gamma| ~ sqrt(2pi) r^{x-1/2} e^{-x} e^{-y th} ; Stirling remainder |R1|<=1/(6r) on Re z>0
    return mp.sqrt(2*mp.pi)*r**(x-mp.mpf('0.5'))*mp.e**(-x - y*th) * mp.e**(-1/(6*r))

print("Test Stirling lower bound for |Gamma(x+iW)| (x=2sigma+1):")
print(f"{'tau':>7}{'sigma':>7}{'|Gamma|exact':>16}{'lowerbnd':>16}{'ratio>=1?':>10}")
worst=mp.mpf('inf')
for taus in ['0.05','0.01','0.002']:
    tau=mp.mpf(taus); W=Wof(tau)
    for sig in [0.5,1.0,2.0,5.0,float(W/2),float(W),float(2*W)]:
        x=2*sig+1
        ge=abs(mp.gamma(mp.mpc(x,float(W))))
        gl=gamma_lower_stirling(x,float(W))
        ratio=ge/gl; worst=min(worst,ratio)
        print(f"{taus:>7}{sig:>7.2f}{mp.nstr(ge,6):>16}{mp.nstr(gl,6):>16}{mp.nstr(ratio,5):>10}")
print(f"worst ratio exact/lower = {mp.nstr(worst,6)}  (>=1 means lower bound valid)")

# Now the cancellation: define the area integral with the LOWER gamma bound (=> UPPER bound on integrand)
print("\nUpper-bounding I_top analytically: integrand_top(sigma) <= |g| * W^{2sigma}/gamma_lower * |pi/sin|")
print(f"{'tau':>7} {'I_top_UB':>12} {'/sqrt(tau)':>12}")
for taus in ['0.05','0.01','0.002']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    def ub(sig):
        x=2*sig+1
        sinabs=abs(mp.sin(mp.pi*mp.mpc(sig,float(W/2))))  # exact
        return 2 * W**(2*sig)/gamma_lower_stirling(x,float(W)) * mp.pi/sinabs
    smax=float(2*W+12); h0=mp.mpf('0.1'); n=int((smax-0.5)/float(h0))
    pts=[ub(0.5+k*float(h0)) for k in range(n+1)]
    A=(mp.fsum(pts)-(pts[0]+pts[-1])/2)*h0
    print(f"{taus:>7} {mp.nstr(A,6):>12} {mp.nstr(A/st,6):>12}")
