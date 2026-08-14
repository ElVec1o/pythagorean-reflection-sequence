"""
MASTER explicit-constant derivation for |T_2| <= C sqrt(tau).

Structure:
  |T_2| <= (1/2pi) oint_{dR} |g_s| * Wcomb(s) * |pi/sin(pi s)| |ds|,   Wcomb=W^{2sigma}/|Gamma(2s+1)|.
Step A (g bound):  |g_s| = |1-e^{-B_s}| <= |B_s| e^{(sqrt2/18)sqrt(tau)}.   (since |1-e^{-z}|<=|z|e^{(Re z)^-})
Step B (B bound):  on dR, |B_s| <= (1/36) tau^2 |4s^3+3s^2-s| * (1+ E_tail),  with the n>=2 tail rel-small.
  We'll bound |B_s| <= K_B * tau^2 * (|s|^3+|s|^2+|s|)   with K_B an explicit constant (>=4/36 ~0.111).
Step C (weighted integral of |s|^3 etc against Wcomb|pi/sin| is O(W^? ) -- combine with tau^2 -> sqrt(tau)).

Define the DIMENSIONLESS integral on the contour, with u = sigma (top) etc, and show
  Q := oint_{dR} (|s|/W)^3 * Wcomb * |pi/sin| |ds|   is BOUNDED (O(1)).
Then tau^2 W^3 = 2 sqrt2 sqrt(tau) gives the sqrt(tau).  Also need lower powers |s|^2,|s| (subdominant).

We compute, EXACT gamma & exact B for the final cross-check:
  R1 := oint |B_s| Wcomb |pi/sin| |ds|      (this is the real quantity, /2pi /sqrt(tau) -> should be O(1))
  and the analytic UPPER bound
  R1_UB := e^{(sqrt2/18)sqrt(tau)} * (1/36) tau^2 * oint (4|s|^3+3|s|^2+|s|)(1+tail) Wcomb |pi/sin| |ds|.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
mp.mp.dps=25
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)

def contour_pts(tau, hstep):
    """yield (s, |ds|) along dR = {Re s=1/2,|Im|<=W/2} U {|Im s|=W/2, Re s>=1/2}.
    By symmetry compute upper half (Im>=0) and double the horizontal; left side full."""
    W=Wof(tau); h=mp.mpf(hstep)
    pts=[]
    # top side Im=W/2, sigma from 1/2 to smax, weight |ds|=dsigma, DOUBLE (bottom side same modulus)
    smax=2*W+12; sig=mp.mpf('0.5')
    while sig<=smax:
        pts.append((mp.mpc(sig,float(W/2)), 2*h)); sig+=h
    # left side Re=1/2, t from -W/2..W/2 -> use symmetry 2*int_0^{W/2}
    t=mp.mpf(0)
    while t<=W/2:
        pts.append((mp.mpc(0.5,float(t)), 2*h)); t+=h
    return pts

print(f"{'tau':>7}{'W':>7}{'R1/2pi':>11}{'/sqrt(t)':>10}{'R1_UB/2pi':>11}{'/sqrt(t)':>10}{'|T2|/st':>9}{'UB>=|T2|':>9}")
from abelplana_verify import S1_bulk
def T2_true(tau):
    q=mp.e**(-tau); w=mp.sqrt(2/tau); W=Wof(tau)
    return S1_bulk(q)-(1-mp.cos(w))-(mp.cos(w)-mp.cos(W))
for taus in ['0.02','0.01','0.005','0.002']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    pts=contour_pts(tau,'0.1')
    R1=mp.mpf(0); R1UB=mp.mpf(0)
    fac=mp.e**((mp.sqrt(2)/18)*st)
    for s,wds in pts:
        Wcomb=W**(2*mp.re(s))/abs(mp.gamma(2*s+1))
        psin=abs(mp.pi/mp.sin(mp.pi*s))
        B=B_gamma(s,tau,2500); g=1-mp.e**(-B)
        R1 += abs(g)*Wcomb*psin*wds
        a=abs(s)
        Bub = fac*(mp.mpf(1)/36)*tau**2*(4*a**3+3*a**2+a)*1.05  # 1.05 absorbs tail; verify below
        R1UB += Bub*Wcomb*psin*wds
    print(f"{taus:>7}{float(W):>7.2f}{mp.nstr(R1/(2*mp.pi),6):>11}{mp.nstr(R1/(2*mp.pi)/st,5):>10}{mp.nstr(R1UB/(2*mp.pi),6):>11}{mp.nstr(R1UB/(2*mp.pi)/st,5):>10}{mp.nstr(abs(T2_true(tau))/st,4):>9}{str(R1UB/(2*mp.pi)>=abs(T2_true(tau))):>9}")
