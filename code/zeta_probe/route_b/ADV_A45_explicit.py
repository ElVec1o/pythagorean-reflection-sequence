"""
A4+A5 EXPLICIT-CONSTANT bound for |T_2| <= C sqrt(tau)  (lem:T2abs, made rigorous & explicit).

Contour dR = boundary of R = {Re s >= 1/2, |Im s| <= W/2}.  By symmetry s <-> conj(s)
(B_{conj s}=conj(B_s), W real) the two horizontal sides contribute equal modulus, and the
left vertical side Re s = 1/2 contributes a third piece.  T_2 real => bound by 2*(top side)+ (left side).

Integrand:  F(s) = |g_s| * W^{2 sigma}/|Gamma(2 sigma+1+iW)|? -- careful, on top side Im s = W/2 so
the gamma argument is 2s+1 = (2 sigma+1) + i W.  On left side Re s=1/2, s=1/2+it, |t|<=W/2,
argument 2s+1 = 2 + 2it.

GOAL: produce explicit constants so that
   |T_2| <= 2*I_top + I_left  <= C * sqrt(tau),   C explicit,
and verify C bounds |T_2|/sqrt(tau) numerically across tau.

We use EXACT |Gamma(x+iy)| via the product |Gamma(x+iy)| = |Gamma(x)| prod_{n>=0}(1+y^2/(x+n)^2)^{-1/2}
to avoid any Stirling-remainder fuss in the NUMERICS, then separately give the analytic explicit-C
derivation in the writeup using a clean Stirling lower bound for |Gamma|.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
from abelplana_verify import S1_bulk
mp.mp.dps = 30
I = mp.mpc(0,1)

def T2_true(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2)
    return S1_bulk(q) - (1-mp.cos(w)) - (mp.cos(w)-mp.cos(W))

def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)

# ---- exact integrand modulus on a point of dR ----
def Fabs(s, tau, K=4000):
    B = B_gamma(s, tau, K)
    g = 1-mp.e**(-B)
    val = g * mp.e**(2*s*mp.log(Wof(tau))) / mp.gamma(2*s+1) * mp.pi/mp.sin(mp.pi*s)
    return abs(val)

def integrate_top(tau, K=4000):
    W = Wof(tau)
    # s = sigma + i W/2, sigma in [1/2, smax]
    smax = float(2*W+12); h0=mp.mpf('0.08')
    n=int((smax-0.5)/float(h0))
    pts=[Fabs(mp.mpc(0.5+k*float(h0), float(W/2)), tau, K) for k in range(n+1)]
    return (mp.fsum(pts)-(pts[0]+pts[-1])/2)*h0

def integrate_left(tau, K=4000):
    W = Wof(tau)
    # s = 1/2 + i t, t in [-W/2, W/2]; integrand symmetric in t -> 2*int_0^{W/2}
    tmax=float(W/2); h0=mp.mpf('0.05')
    n=max(2,int(tmax/float(h0)))
    h0=mp.mpf(tmax)/n
    pts=[Fabs(mp.mpc(0.5, k*float(h0)), tau, K) for k in range(n+1)]
    half=(mp.fsum(pts)-(pts[0]+pts[-1])/2)*h0
    return 2*half

print("Numerical contour-integral pieces (exact integrand), |T_2| <= (1/2pi)(2 I_top + I_left):")
print(f"{'tau':>7} {'W':>8} {'I_top':>11} {'I_left':>11} {'bound':>11} {'bnd/sqrt(t)':>12} {'|T2|/sqrt(t)':>12} {'ok?':>5}")
for taus in ['0.05','0.02','0.01','0.005','0.002']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    It=integrate_top(tau); Il=integrate_left(tau)
    bound=(2*It+Il)/(2*mp.pi)
    T2=abs(T2_true(tau))
    print(f"{taus:>7} {float(W):>8.3f} {mp.nstr(It,6):>11} {mp.nstr(Il,6):>11} {mp.nstr(bound,6):>11} {mp.nstr(bound/st,6):>12} {mp.nstr(T2/st,6):>12} {str(bound>=T2):>5}")
