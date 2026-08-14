"""
lemcos_Bstrip.py  --  numerical certificate for Lemma lem:Bbounded (transcendence.tex).

Claim: Re B_s is bounded BELOW on the strip S = {0 <= Im s <= W/2, Re s >= 0}, because
W/2 = (1/sqrt2) tau^{-1/2} < pi/tau, so there is NO resonance (all |t +- pi k/tau| >= pi/tau - W/2 > 0)
and the divergent -pi^2 k/tau Stirling terms cancel exactly between the s-shifted and boundary Gammas.
The Re B_s -> -inf disaster happens only at the resonance Im s ~ pi/tau >> W/2, OFF the strip.

This is the single finiteness V_Gamma(A) < inf that upgrades lem:extremephase from conditional to
a proof modulo Olver's steepest-descent theorem, hence makes V transcendental conditional only on
that cited classical result.  See memory lemcos-tail-proof-flaw.md.

Cross-checks the Gamma-form B_s against the form-factor (phi) sum at integer s, and against the
saddle value B(s*) ~ -i (sqrt2/36) sqrt(tau).
"""
import mpmath as mp
mp.mp.dps = 30


def phi(y):
    return mp.log(mp.sinh(y / 2) / (y / 2))


def B_direct(s, tau):
    """form-factor sum, valid at integer s >= 0."""
    return sum(phi((2 * i + 2) * tau) + phi((2 * i + 1) * tau) - phi(tau)
               for i in range(int(s)))


def B_gamma(s, tau, K=6000):
    """analytic-continuation Gamma form, valid for Re s >= 0 (any complex s)."""
    tot = mp.mpf(0)
    for k in range(1, K + 1):
        a = mp.mpc(0, mp.pi * k / tau)
        for c in (1, 2):
            tot += (2 * s * mp.log(tau / (mp.pi * k))
                    + mp.loggamma(s + mp.mpf(c) / 2 + a) + mp.loggamma(s + mp.mpf(c) / 2 - a)
                    - mp.loggamma(mp.mpf(c) / 2 + a) - mp.loggamma(mp.mpf(c) / 2 - a))
        tot -= s * mp.log(1 + (tau / (2 * mp.pi * k)) ** 2)
    return tot


def main():
    tau = mp.mpf('0.05')
    W = mp.sqrt(2 / tau)
    print(f"tau={tau}  W={mp.nstr(W,6)}  W/2={mp.nstr(W/2,6)}  pi/tau={mp.nstr(mp.pi/tau,6)} (resonance)")
    print(f"W/2 < pi/tau ?  {W/2 < mp.pi/tau}   (always true for tau < 2 pi^2)")

    print("\n=== cross-check B_gamma vs B_direct at integer s ===")
    for s in (3, 6):
        bg, bd = B_gamma(s, tau), B_direct(s, tau)
        print(f"  s={s}: B_gamma={mp.nstr(bg,10)}  B_direct={mp.nstr(bd,10)}  |diff|={mp.nstr(abs(bg-bd),3)}")

    print("\n=== saddle value B(s*),  s*=iW/2  (expect ~ -i (sqrt2/36) sqrt(tau)) ===")
    sstar = mp.mpc(0, W / 2)
    print(f"  B(s*)={mp.nstr(B_gamma(sstar,tau),8)}   target={mp.nstr(-1j*mp.sqrt(2)/36*mp.sqrt(tau),8)}")

    print("\n=== Re B_s on the STRIP  (Im s <= W/2): bounded BELOW ===")
    for t in [mp.mpf('0'), mp.mpf('1'), W / 2]:
        row = [float(mp.re(B_gamma(mp.mpc(sig, t), tau))) for sig in (mp.mpf('0.5'), 2, 5, 15)]
        print(f"  Im s={mp.nstr(t,4):>6}: Re B at Re s=0.5,2,5,15 -> " + str([f'{x:.3f}' for x in row]))

    print("\n=== Re B_s in the DANGER zone (Im s near/above pi/tau): dives to -inf ===")
    for t in [mp.mpf('30'), mp.mpf('50'), mp.pi / tau, mp.mpf('80')]:
        print(f"  Im s={mp.nstr(t,5):>7}: Re B(0.5+it)= {mp.nstr(mp.re(B_gamma(mp.mpc('0.5',t),tau)),6)}")


if __name__ == "__main__":
    main()
