import mpmath as mp
mp.mp.dps = 30
# Verify the Poisson/modular asymptotic of Morita's theta theta_p(y)=sum_{n in Z} p^{n(n-1)/2} y^n,
# for y = -p^b/x, p=e^{-eps}.  Claim:
#   theta_p(-p^b/x) = e^{(eps/2)c^2} sqrt(2pi/eps) sum_k e^{(theta0-2pi i k)^2/(2eps)} e^{-c(theta0-2pi i k)}
# with c=b-1/2, theta0 = i pi - log x.   The e^{(eps/2)c^2} is the SUBLEADING (b-dependent) factor.
def theta_exact(y, eps, N=4000):
    p = mp.e**(-eps)
    return mp.fsum(p**(mp.mpf(n*(n-1))/2) * y**n for n in range(-N,N+1))
def theta_poisson(b, x, eps, K=6):
    c = b - mp.mpf(1)/2
    th0 = 1j*mp.pi - mp.log(x)
    pref = mp.e**((eps/2)*c*c) * mp.sqrt(2*mp.pi/eps)
    s = mp.fsum( mp.e**((th0-2j*mp.pi*k)**2/(2*eps)) * mp.e**(-c*(th0-2j*mp.pi*k)) for k in range(-K,K+1))
    return pref*s
print("Check theta_p(-p^b/x) exact vs Poisson:")
for (eps,b,x) in [(mp.mpf('0.4'),5,10),(mp.mpf('0.3'),5,10),(mp.mpf('0.4'),mp.mpf('3.5'),10),(mp.mpf('0.3'),3.5,30)]:
    p = mp.e**(-eps); y = -p**b/x
    ex = theta_exact(y,eps); po = theta_poisson(b,x,eps)
    print(f"  eps={float(eps):.2f} b={float(b):.1f} x={x}: exact={mp.nstr(ex,8)}  poisson={mp.nstr(po,8)}  rel.diff={mp.nstr(abs(ex-po)/abs(ex),3)}")

print()
print("Now the QUOTIENT subleading factor for nu=3/2:  e^{(eps/2)(c_{2nu+2}^2 - c_{nu+2}^2)} = e^{(eps/2)*3nu(nu+1)}")
nu = mp.mpf(3)/2
b1, b2 = 2*nu+2, nu+2
c1, c2 = b1-mp.mpf(1)/2, b2-mp.mpf(1)/2
print(f"  predicted exponent coeff (eps/2)*(c1^2-c2^2): 3nu(nu+1)/2 = {float(3*nu*(nu+1)/2)}  (so factor e^[{float(3*nu*(nu+1)/2)} eps])")
print(f"  in tau (eps=tau/2): relative subleading = {float(3*nu*(nu+1)/2)}*tau/2 = {float(3*nu*(nu+1)/4)} tau")
# numerically extract the quotient's subleading by dividing out the leading (c-dependent, no e^{(eps/2)c^2}) part
for eps in [mp.mpf('0.2'),mp.mpf('0.1'),mp.mpf('0.05')]:
    x = 50
    p = mp.e**(-eps)
    Q = theta_exact(-p**b1/x,eps)/theta_exact(-p**b2/x,eps)
    th0 = 1j*mp.pi - mp.log(x); E = mp.e**(2j*mp.pi*mp.log(x)/eps)
    lead = mp.e**(-(c1-c2)*th0) * (1+mp.e**(2j*mp.pi*c1)*E)/(1+mp.e**(2j*mp.pi*c2)*E)
    resid = Q/lead
    print(f"  eps={float(eps):.3f}: quotient/leading = {mp.nstr(resid,8)}   predicted e^[3nu(nu+1)/2 * eps]={mp.nstr(mp.e**(3*nu*(nu+1)/2*eps),8)}")
