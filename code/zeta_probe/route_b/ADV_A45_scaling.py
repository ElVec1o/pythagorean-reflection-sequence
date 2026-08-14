import mpmath as mp
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)
# Compare the EXACT |pi/sin(pi s)| on top side vs the explicit majorant 2 pi e^{-pi W/2}.
# sin(pi(sigma+iW/2)) = sin(pi sigma)cosh(pi W/2)+i cos(pi sigma)sinh(pi W/2)
# |sin|^2 = sin^2(pi sigma)cosh^2 + cos^2 sinh^2 = sinh^2(pi W/2) + sin^2(pi sigma)
# so |sin(pi s)| >= sinh(pi W/2), hence |pi/sin| <= pi/sinh(pi W/2) <= 2 pi e^{-pi W/2}/(1-e^{-pi W}).
for taus in ['0.05','0.01','0.002']:
    tau=mp.mpf(taus); W=Wof(tau)
    maj = mp.pi/mp.sinh(mp.pi*W/2)
    clean = 2*mp.pi*mp.e**(-mp.pi*W/2)/(1-mp.e**(-mp.pi*W))
    print(f"tau={taus} W={float(W):.3f}  pi/sinh(piW/2)={mp.nstr(maj,5)} clean_maj={mp.nstr(clean,5)} epiW/2={mp.nstr(mp.e**(-mp.pi*W/2),5)}")
print()
# So integrand_top <= 2 * W^{2sigma}/gamma_lower * 2 pi e^{-pi W/2}/(1-e^{-piW})
# The key combination C(sigma) = W^{2sigma} e^{-pi W/2}/|Gamma(2sigma+1+iW)|.
# With gamma_lower = sqrt(2pi) r^{x-1/2} e^{-x - W arctan(W/x)}, x=2sigma+1, r=sqrt(x^2+W^2).
# Let's compute the area  J = int_{1/2}^inf W^{2sigma} e^{-pi W/2}/|Gamma(2sigma+1+iW)| dsigma   EXACT gamma,
# and J/sqrt(tau).
print("J = int W^{2sigma} e^{-piW/2}/|Gamma(2sigma+1+iW)| dsigma  (EXACT gamma):")
for taus in ['0.05','0.01','0.002','0.0005']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    def f(sig):
        return W**(2*sig)*mp.e**(-mp.pi*W/2)/abs(mp.gamma(mp.mpc(2*sig+1,float(W))))
    smax=float(2*W+12); h0=mp.mpf('0.1'); n=int((smax-0.5)/float(h0))
    pts=[f(0.5+k*float(h0)) for k in range(n+1)]
    J=(mp.fsum(pts)-(pts[0]+pts[-1])/2)*h0
    # locate peak
    sigpeak = max(range(n+1), key=lambda k: pts[k])*float(h0)+0.5
    print(f"tau={taus} W={float(W):.2f} J={mp.nstr(J,6)} J/sqrt(tau)={mp.nstr(J/st,6)} peak@sigma={sigpeak:.2f} (W/2={float(W/2):.2f})")
