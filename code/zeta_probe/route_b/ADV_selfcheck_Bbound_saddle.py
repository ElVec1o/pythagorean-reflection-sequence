"""
Self-verification of the two agent findings before rewriting the doc:
 (A) lem:Bbounded sharp bound = -(sqrt2/18) sqrt(tau), minimized at the DIAGONAL s=(W/2)(1+i),
     and Re B_s is NON-monotone in sigma along t=W/2 (dips then rises) -- the doc's "increasing in
     sigma" is false.
 (B) saddle of Phi(s)=2s log W - logGamma(2s+1) - log sin(pi s) sits at Re s = -1/4 (not on iR),
     Phi''~ -4/W; and along the HORIZONTAL contour Im s = W/2, Re(analytic Phi) is monotone
     decreasing with bounded prefactor (the operative stationary-phase contour).
Scalar mpmath, dps 40, modest K, memory-safe.
"""
import mpmath as mp
mp.mp.dps = 40

def B_gamma(s, tau, K=3000):
    tot = mp.mpf(0)
    for k in range(1, K + 1):
        a = mp.mpc(0, mp.pi * k / tau)
        for c in (1, 2):
            tot += (2*s*mp.log(tau/(mp.pi*k))
                    + mp.loggamma(s+mp.mpf(c)/2+a) + mp.loggamma(s+mp.mpf(c)/2-a)
                    - mp.loggamma(mp.mpf(c)/2+a) - mp.loggamma(mp.mpf(c)/2-a))
        tot -= s*mp.log(1+(tau/(2*mp.pi*k))**2)
    return tot

print("=== (A) lem:Bbounded: bound is sqrt(tau), minimizer at diagonal (W/2)(1+i) ===")
print(f"{'tau':>8} {'ReB at (W/2)(1+i)':>20} {'/sqrt(tau)':>12} {'-sqrt2/18=':>12} {'ReB at iW/2 (corner)':>22}")
target = -mp.sqrt(2)/18
for taus in ['0.05','0.02','0.01','0.005']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau)
    sdiag = mp.mpc(W/2, W/2)            # diagonal saddle
    scorner = mp.mpc(0, W/2)           # imaginary-axis corner
    bd = mp.re(B_gamma(sdiag, tau)); bc = mp.re(B_gamma(scorner, tau))
    print(f"{taus:>8} {mp.nstr(bd,8):>20} {mp.nstr(bd/mp.sqrt(tau),7):>12} {mp.nstr(target,7):>12} {mp.nstr(bc,8):>22}")

print("\n=== (A') sigma-monotonicity along t=W/2 is FALSE (dip then rise) ===")
tau = mp.mpf('0.02'); W = mp.sqrt(2/tau)
print(f"tau={float(tau)}, W={float(W):.4f}, W/2={float(W/2):.4f}")
print(f"{'sigma':>8} {'Re B(sigma+iW/2)':>18}")
for sig in [mp.mpf(x) for x in ['0','1','2','3','4.95','7','10','20','40']]:
    print(f"{float(sig):>8} {mp.nstr(mp.re(B_gamma(mp.mpc(sig,W/2),tau)),8):>18}")

print("\n=== (B) saddle of Phi(s)=2s logW - logGamma(2s+1) - log sin(pi s): Re s = -1/4? ===")
def Phi(s, W): return 2*s*mp.log(W) - mp.loggamma(2*s+1) - mp.log(mp.sin(mp.pi*s))
for taus in ['0.05','0.02','0.01']:
    tau = mp.mpf(taus); W = mp.sqrt(2/tau)*mp.e**(-tau/2)
    sad = mp.findroot(lambda s: mp.diff(lambda z: Phi(z,W), s), mp.mpc('-0.25', float(W/2)))
    d2 = mp.diff(lambda z: Phi(z,W), sad, 2)
    print(f"  tau={taus}: saddle={mp.nstr(sad,8)}  (W/2={mp.nstr(W/2,6)})  Phi''={mp.nstr(d2,6)}  Phi''*W/(-4)={mp.nstr(d2*W/(-4),6)}")

print("\n=== (B') horizontal contour Im s=W/2: Re(analytic Phi) monotone-decreasing in sigma? ===")
tau = mp.mpf('0.02'); W = mp.sqrt(2/tau)*mp.e**(-tau/2)
prev = None; mono = True; maxup = mp.mpf(0)
for i in range(0, 40):
    sig = mp.mpf(i)/3
    val = mp.re(Phi(mp.mpc(sig, W/2), W))
    if prev is not None and val > prev: maxup = max(maxup, val-prev); mono=False
    prev = val
print(f"  Re Phi monotone-decreasing along Im s=W/2 ? {mono}   (max upward step {mp.nstr(maxup,4)})")
print("  (analytic part only; log|g_s| adds an O(sqrt tau) bump near sigma=0 per agent B)")
