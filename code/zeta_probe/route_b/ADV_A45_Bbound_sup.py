"""
Explicit |B_s| <= c0 sqrt(tau) on dR, and the O(1) contour-combination integral.
We need SUP_{dR} |B_s| / sqrt(tau).  dR has 3 parts but B continues analytically; B real-symmetric.
We check sup over top side (sigma>=1/2, Im=W/2), left side (Re=1/2, |Im|<=W/2).
Claim: |B_s| <= c0 sqrt(tau) with c0 explicit.  From B_s = sum phi_n tau^{2n}(P_n(2s)-s), leading
n=1: (1/36)tau^2|4s^3+3s^2-s|.  On dR, |s| <= |W/2+iW/2| = W/sqrt2 (top corner) ... actually max |s|
on dR is at top-right going to infinity, BUT weighted by 1/Gamma it decays. The RELEVANT sup of |B_s|
is where Wcomb is non-negligible, i.e. sigma=O(W). At |s| ~ W, |B_s| ~ (1/36)tau^2 (2W)^3*?  Let's just
measure sup |B_s|/sqrt(tau) over the region sigma in [1/2, 3W], and the FULL weighted integral.
"""
import mpmath as mp
from lemcos_Bstrip import B_gamma
mp.mp.dps=30
def Wof(tau): return mp.sqrt(2/tau)*mp.e**(-tau/2)

print("sup over dR of |B_s|/sqrt(tau), and of |g_s|/sqrt(tau), restricted to sigma<=3W (mass region):")
for taus in ['0.02','0.01','0.005','0.002']:
    tau=mp.mpf(taus); W=Wof(tau); st=mp.sqrt(tau)
    supB=mp.mpf(0); supg=mp.mpf(0)
    # top side
    sig=mp.mpf('0.5')
    while sig<=3*W:
        s=mp.mpc(sig,float(W/2)); B=B_gamma(s,tau,3000); g=1-mp.e**(-B)
        supB=max(supB,abs(B)/st); supg=max(supg,abs(g)/st); sig+=mp.mpf('0.5')
    # left side
    t=mp.mpf(0)
    while t<=W/2:
        s=mp.mpc(0.5,float(t)); B=B_gamma(s,tau,3000); g=1-mp.e**(-B)
        supB=max(supB,abs(B)/st); supg=max(supg,abs(g)/st); t+=mp.mpf('0.5')
    print(f"tau={taus} W={float(W):.2f}: sup|B|/sqrt(tau)={mp.nstr(supB,6)} sup|g|/sqrt(tau)={mp.nstr(supg,6)}")
