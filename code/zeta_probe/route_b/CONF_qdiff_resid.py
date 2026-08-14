import mpmath as mp
mp.mp.dps=40
# eq:qdiff operator:  D[Y](x) = Y(qx) - (1+q^3-2(1-q)q^2 x^2) Y(x) + q^3 Y(x/q)
# Test residual of the Bessel approximant Y_app(x)=x^{3/2} J_{3/2}(W x), W=w e^{-tau/2}, near x=1 (the pole region).
def Jbess(nu,z): return mp.besselj(nu,z)
def qdiff_resid(Yfun,q,x):
    return Yfun(q*x) - (1+q**3-2*(1-q)*q**2*x**2)*Yfun(x) + q**3*Yfun(x/q)
print(f"{'tau':>9}{'w':>8}  residual/Y_app at x=1   (target: O(tau^2))   ratio resid/tau^2")
for taus in ['0.04','0.02','0.01','0.005','0.0025']:
    tau=mp.mpf(taus);q=mp.e**(-tau);w=mp.sqrt(2/tau);W=w*mp.e**(-tau/2)
    Yapp=lambda x: x**mp.mpf('1.5')*Jbess(mp.mpf(3)/2,W*x)
    x=mp.mpf(1)
    r=qdiff_resid(Yapp,q,x); rel=r/Yapp(x)
    print(f"{taus:>9}{float(w):>8.4f}  rel={mp.nstr(rel,8):>16}   resid/tau^2={mp.nstr(rel/tau**2,6)}")
print("\nAlso test the NAIVE argument w (not shifted W) to confirm the shift matters:")
for taus in ['0.02','0.01','0.005']:
    tau=mp.mpf(taus);q=mp.e**(-tau);w=mp.sqrt(2/tau)
    Yapp_w=lambda x: x**mp.mpf('1.5')*Jbess(mp.mpf(3)/2,w*x)
    rel=qdiff_resid(Yapp_w,q,mp.mpf(1))/Yapp_w(mp.mpf(1))
    print(f"  tau={taus}: naive-w rel residual={mp.nstr(rel,6)}  /tau={mp.nstr(rel/tau,5)} (=> O(tau) if shift needed)")
