"""
BOUND 3 (clean route): is |T_2| <= integral_{Im s = W/2} |h(s) pi/sin(pi s)| d sigma = O(sqrt tau)?
If yes, V closes by an ABSOLUTE bound on the horizontal contour -- no van der Corput, no Poisson aliases,
no oscillation cancellation. h(s)=g_s W^{2s}/Gamma(2s+1), g_s=1-e^{-B_s}.
On Im s=W/2 the e^{pi W/2} factors cancel (1/|Gamma(1+iW)| ~ e^{piW/2}, |pi/sin| ~ e^{-piW/2}), so the
absolute integrand is small (~sqrt tau near sigma=0) -- UNLIKE the real axis (majorant cosh W ~ e^W).
Checks:
 (1) A = int_0^inf |h(sigma+iW/2) pi/sin(pi(sigma+iW/2))| d sigma ;  is A/sqrt(tau) BOUNDED?
 (2) deformation valid? signed line integral reproduces T_2_true (so the abs bound is legitimate).
Scalar mpmath, dps 30, memory-safe.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
from abelplana_verify import S1_bulk
mp.mp.dps = 30
I = mp.mpc(0,1)

def T2_true(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    return S1_bulk(q) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def h(s, tau, K=2500):
    B = B_gamma(s, tau, K)
    return (1-mp.e**(-B)) * mp.e**(2*s*mp.log(mp.sqrt(2/tau)*mp.e**(-tau/2))) / mp.gamma(2*s+1)

def integrand_abs(sig, tau, W):
    s = mp.mpc(sig, float(W/2))
    val = h(s, tau) * mp.pi/mp.sin(mp.pi*s)
    return abs(val)

print(f"{'tau':>8} {'W':>9} {'A=int|h pi/sin|':>18} {'A/sqrt(tau)':>13} {'T2_true':>14} {'|T2|/sqrt(tau)':>14} {'A>=|T2|?':>9}")
for taus in ['0.05','0.02','0.01','0.005']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau)*mp.e**(-tau/2)
    # integrate sigma in [0, smax]; integrand decays for large sigma (factorial). step h0.
    smax = float(2*W + 10); h0 = mp.mpf('0.1')
    n = int(smax/float(h0))
    pts = [integrand_abs(k*h0, tau, W) for k in range(n+1)]
    A = (mp.fsum(pts) - (pts[0]+pts[-1])/2)*h0    # trapezoid
    T2 = T2_true(tau); st=mp.sqrt(tau)
    print(f"{taus:>8} {float(W):>9.4f} {mp.nstr(A,8):>18} {mp.nstr(A/st,7):>13} {mp.nstr(T2,7):>14} {mp.nstr(abs(T2)/st,7):>14} {str(A>=abs(T2)):>9}")
print()
print("If A/sqrt(tau) is BOUNDED and A >= |T2|: then |T2| <= A = O(sqrt tau) RIGOROUSLY by absolute value,")
print("no van der Corput / no alias decay needed. (Still must confirm the contour deformation C -> {Im s=W/2}")
print("is valid -- no poles crossed in 0<Im s<W/2 for Re s>=0, which holds since g_s analytic there.)")
