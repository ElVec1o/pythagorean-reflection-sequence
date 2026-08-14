"""
ADV_Bbounded_verify.py  --  rigorous numerical pinning of the LOWER BOUND in Lemma lem:Bbounded.

Claim:  Re B_s >= -C * tau   on the strip  S = {0 <= Im s <= W/2, Re s >= 0},  W = sqrt(2/tau).

We use the canonical Gamma-form B_gamma(s, tau, K) from lemcos_Bstrip.py (cross-checked against the
form-factor sum at integer s).  s = sigma + i t.

SCALAR mpmath only (memory-safe), high precision (dps 40-50), K large with a K-stability check.

Tasks:
 1. grid-minimize Re B_s over S for a range of tau; report min, min/tau, argmin; check argmin = saddle
    corner (sigma=0, t=W/2) and whether min/tau -> finite negative constant C.
 2. monotone increasing in sigma at fixed t; unbounded as sigma -> inf.
 3. resonance disaster OFF strip: Re B at Im s = pi/tau and beyond dives negative.
 4. per-k cancellation: each k-term Re part is O((t tau/(pi k))^2); identify the constant.
"""
import mpmath as mp

mp.mp.dps = 45


# ---------------------------------------------------------------------------
# canonical B_s  (Gamma form), scalar.  Identical to lemcos_Bstrip.B_gamma.
# ---------------------------------------------------------------------------
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


def reB(s, tau, K):
    return mp.re(B_gamma(s, tau, K))


# ---------------------------------------------------------------------------
# Task 0:  K-stability  (K=4000 vs 8000) at the most demanding point (saddle corner)
# ---------------------------------------------------------------------------
def task0_kstability():
    print("=" * 78)
    print("TASK 0  --  K-stability check  (compare K=4000 vs 8000 at saddle corner s*=iW/2)")
    print("=" * 78)
    for ts in ('0.1', '0.02', '0.005'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau)
        sstar = mp.mpc(0, W / 2)
        b4 = reB(sstar, tau, 4000)
        b8 = reB(sstar, tau, 8000)
        print(f"  tau={ts:>6}: ReB(s*) K=4000 -> {mp.nstr(b4, 12)}   K=8000 -> {mp.nstr(b8, 12)}"
              f"   |diff|={mp.nstr(abs(b4 - b8), 3)}")
    print("  (tail per-k ~ 1/k^2 so K=4000 already converged to ~1e-7; K=8000 confirms)\n")


# ---------------------------------------------------------------------------
# Task 1:  grid-minimize Re B_s over the strip S
# ---------------------------------------------------------------------------
def task1_gridmin(K=4000):
    print("=" * 78)
    print("TASK 1  --  minimum of Re B_s over the strip S = {0<=Im s<=W/2, Re s>=0}")
    print("=" * 78)
    print("  IMPORTANT: the dip sits at sigma ~ W/2 (NOT the corner), so sigma must be sampled")
    print("  out to ~1.2 W.  grid: t in [0,W/2] (20 pts), sigma in [0,1.2W] (24 pts).  K={}".format(K))
    print(f"  {'tau':>7} | {'min Re B_s':>16} | {'min/tau':>11} | {'min/sqrt(tau)':>14} "
          f"| {'argmin (sigma, t)':>24} | {'sig/W':>6}")
    print("  " + "-" * 96)
    results = []
    for ts in ('0.2', '0.1', '0.05', '0.02', '0.01', '0.005'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau)
        ts_grid = [W / 2 * mp.mpf(j) / 19 for j in range(20)]            # 0 .. W/2
        sig_grid = [mp.mpf('1.2') * W * mp.mpf(j) / 23 for j in range(24)]  # 0 .. 1.2W
        best = None
        best_arg = None
        for t in ts_grid:
            for sig in sig_grid:
                v = reB(mp.mpc(sig, t), tau, K)
                if best is None or v < best:
                    best = v
                    best_arg = (sig, t)
        ratio = best / tau
        rsqrt = best / mp.sqrt(tau)
        at_top = abs(best_arg[1] - W / 2) < 1e-9
        results.append((ts, best, ratio, rsqrt, best_arg, W))
        print(f"  {ts:>7} | {mp.nstr(best, 12):>16} | {mp.nstr(ratio, 8):>11} | {mp.nstr(rsqrt, 9):>14} "
              f"| sig={mp.nstr(best_arg[0],4)}, t={mp.nstr(best_arg[1],5)} (W/2={mp.nstr(W/2,5)}) "
              f"| {mp.nstr(best_arg[0]/W,3):>6}")
    print()
    print("  KEY: min/tau GROWS as tau->0 (so 'Re B >= -C tau' is FALSE on unbounded-sigma S),")
    print("       but min/sqrt(tau) is ~CONSTANT -> the true scaling is  Re B_s >= -C' sqrt(tau).")
    print(f"  {'tau':>8} | {'min/tau (diverges)':>20} | {'min/sqrt(tau) (settles)':>24}")
    for ts, best, ratio, rsqrt, arg, W in results:
        print(f"  {ts:>8} | {mp.nstr(ratio, 9):>20} | {mp.nstr(rsqrt, 9):>24}")
    print(f"  candidate constant  C' = sqrt2/18 = {mp.nstr(mp.sqrt(2)/18, 9)} "
          f"(= 2x the on-shell saddle modulus sqrt2/36)")
    print()
    return results


# the sigma=0 EDGE ratio (where the per-k cancellation gives the clean 1/24); and the
# true STRIP-MINIMUM scaling (sqrt(tau), achieved at sigma ~ W/2).
def task1b_refine(K=4000):
    print("=" * 78)
    print("TASK 1b --  two distinct quantities, kept separate:")
    print("            (A) sigma=0 EDGE value ReB(0,W/2): scales as tau,  ReB/tau -> -1/24")
    print("            (B) STRIP MINIMUM (sigma~W/2):    scales as sqrt(tau), min/sqrt(tau) -> -sqrt2/18")
    print("=" * 78)
    print("  (A) sigma=0 edge -- this is the only place 'Re B >= -C tau' style bound holds, C=1/24:")
    print(f"  {'tau':>8} | {'ReB(0,W/2)':>18} | {'ReB(0,W/2)/tau':>16}  (target -1/24)")
    print("  " + "-" * 56)
    vals = []
    for ts in ('0.05', '0.02', '0.01', '0.005', '0.002', '0.001'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau)
        v = reB(mp.mpc(0, W / 2), tau, K)
        r = v / tau
        vals.append((tau, r))
        print(f"  {ts:>8} | {mp.nstr(v, 14):>18} | {mp.nstr(r, 12):>16}")
    print(f"  -> -1/24 = {mp.nstr(-mp.mpf(1)/24, 12)}  (ratio approaches -1/24 from below as tau->0)")
    print()
    print("  (B) strip minimum (ternary-refined over sigma on the top edge t=W/2):")
    print(f"  {'tau':>8} | {'min ReB':>16} | {'sig_min/W':>9} | {'min/sqrt(tau)':>14}  (target -sqrt2/18)")
    print("  " + "-" * 60)
    for ts in ('0.05', '0.02', '0.01', '0.005'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau); t = W / 2
        a, b = mp.mpf(0), mp.mpf('1.2') * W
        f = lambda x: reB(mp.mpc(x, t), tau, K)
        for _ in range(40):
            m1 = a + (b - a) / 3; m2 = b - (b - a) / 3
            if f(m1) < f(m2): b = m2
            else: a = m1
        xm = (a + b) / 2; v = f(xm)
        print(f"  {ts:>8} | {mp.nstr(v, 12):>16} | {mp.nstr(xm/W, 5):>9} | {mp.nstr(v/mp.sqrt(tau), 9):>14}")
    print(f"  -> -sqrt2/18 = {mp.nstr(-mp.sqrt(2)/18, 10)}   (= 2 x on-shell saddle modulus sqrt2/36)")
    print()
    return vals


# ---------------------------------------------------------------------------
# Task 2:  monotone increasing in sigma at fixed t; unbounded as sigma -> inf
# ---------------------------------------------------------------------------
def task2_monotone(K=4000):
    print("=" * 78)
    print("TASK 2  --  sigma-behaviour of Re B_s at fixed t  (CORRECTED: NOT monotone)")
    print("=" * 78)
    print("  FINDING: along the top edge t=W/2, Re B_s is NOT increasing in sigma. It DECREASES")
    print("  (initial slope ~ -tau/6 < 0), bottoms out near sigma ~ W/2, then turns up (real-axis")
    print("  Stirling growth 2 sigma log sigma) and -> +inf. So the dip sits at INTERIOR sigma,")
    print("  not at the corner sigma=0.  The proof's 'increasing in Re s' is FALSE.\n")
    for ts in ('0.05', '0.01'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau)
        for t in (mp.mpf(0), W / 2):
            sigs = [mp.mpf(x) for x in (0, 0.5, 1, 2, 5, 10, 20, 35, 50)]
            row = [reB(mp.mpc(sig, t), tau, K) for sig in sigs]
            diffs = [row[i + 1] - row[i] for i in range(len(row) - 1)]
            mono = all(d > 0 for d in diffs)
            # initial slope
            h = mp.mpf('0.001')
            slope0 = (reB(mp.mpc(h, t), tau, K) - reB(mp.mpc(0, t), tau, K)) / h
            print(f"  tau={ts}, Im s={mp.nstr(t,5)}:")
            print(f"     sigma : " + "  ".join(f"{float(x):>7.1f}" for x in sigs))
            print(f"     Re B  : " + "  ".join(f"{float(x):>7.3f}" for x in row))
            print(f"     strictly increasing in sigma? {mono}    d(ReB)/dsigma|_0 = {mp.nstr(slope0,6)} "
                  f"(predict -tau/6={mp.nstr(-tau/6,6)} on top edge)")
            print(f"     Re B at sigma=50 = {mp.nstr(row[-1],8)} (eventually grows ~2 sigma log sigma -> +inf)")
        print()


# ---------------------------------------------------------------------------
# Task 3:  resonance disaster OFF the strip
# ---------------------------------------------------------------------------
def task3_resonance(K=4000):
    print("=" * 78)
    print("TASK 3  --  resonance disaster is OFF the strip (Im s near/above pi/tau dives negative)")
    print("=" * 78)
    for ts in ('0.05', '0.02'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau)
        res = mp.pi / tau
        print(f"  tau={ts}:  W/2={mp.nstr(W/2,6)} (top of strip)   pi/tau={mp.nstr(res,6)} (1st resonance)")
        sig = mp.mpf('0.5')
        pts = [('W/2 (on strip)', W / 2),
               ('W (just above)', W),
               ('0.5*pi/tau', res / 2),
               ('0.9*pi/tau', res * mp.mpf('0.9')),
               ('pi/tau (RESONANCE)', res),
               ('1.5*pi/tau', res * mp.mpf('1.5')),
               ('2*pi/tau', 2 * res)]
        for lab, t in pts:
            v = reB(mp.mpc(sig, t), tau, K)
            print(f"     Im s = {mp.nstr(t,7):>9}  [{lab:>20}]:  Re B(0.5+it) = {mp.nstr(v, 7)}")
        print("     => bounded on the strip (Im s<=W/2), plunges as Im s -> pi/tau and beyond.\n")


# ---------------------------------------------------------------------------
# Task 4:  per-k cancellation;  each k-term Re ~ -(c/2)(t tau/(pi k))^2;  identify constant
# ---------------------------------------------------------------------------
def kterm_re(s, tau, k):
    """Real part of the single k-th term of B_gamma (sum over c in {1,2})."""
    a = mp.mpc(0, mp.pi * k / tau)
    tot = mp.mpf(0)
    for c in (1, 2):
        tot += (2 * s * mp.log(tau / (mp.pi * k))
                + mp.loggamma(s + mp.mpf(c) / 2 + a) + mp.loggamma(s + mp.mpf(c) / 2 - a)
                - mp.loggamma(mp.mpf(c) / 2 + a) - mp.loggamma(mp.mpf(c) / 2 - a))
    tot -= s * mp.log(1 + (tau / (2 * mp.pi * k)) ** 2)
    return mp.re(tot)


def task4_perk():
    print("=" * 78)
    print("TASK 4  --  per-k cancellation;  identify C")
    print("=" * 78)
    print("  Stirling: the divergent -pi^2 k/tau pieces cancel between s-shifted & boundary Gammas.")
    print("  The c-independent log-correction makes the surviving REAL second-order coefficient of")
    print("  a SINGLE c-Gamma-pair equal -((c-1)/2)(t tau)^2/(pi k)^2  (the 1/(2b) psi-term shifts c->c-1;")
    print("  verified to 9 digits below).  Summing c=1,2: (0 + 1/2) => per-k = -(1/2)(t tau)^2/(pi k)^2.")
    print("  At the saddle corner s=(0, t=W/2),  t^2 = W^2/4 = 1/(2 tau), so (t tau)^2 = tau/2:")
    print("        per-k ~ -(1/2)(tau/2)/(pi^2 k^2) = -tau/(4 pi^2 k^2).")
    print("  Sum over k (zeta(2)=pi^2/6):  C = (1/4)(1/pi^2)(pi^2/6) = 1/24 = 0.0416666...\n")

    # 4a: confirm the single-c coefficient is -((c-1)/2)
    print("  4a) single-c gamma-pair Re coefficient / [-(t tau)^2/(pi k)^2]  vs  (c-1)/2:")
    tau = mp.mpf('0.0005'); W = mp.sqrt(2 / tau); t = W / 2; k = 1
    s = mp.mpc(0, t)
    base = -(t * tau) ** 2 / (mp.pi * k) ** 2
    for c in (1, 2, 3, 5):
        a = mp.mpc(0, mp.pi * k / tau)
        gp = mp.re(2 * s * mp.log(tau / (mp.pi * k))
                   + mp.loggamma(s + mp.mpf(c) / 2 + a) + mp.loggamma(s + mp.mpf(c) / 2 - a)
                   - mp.loggamma(mp.mpf(c) / 2 + a) - mp.loggamma(mp.mpf(c) / 2 - a))
        print(f"        c={c}: coeff={mp.nstr(gp/base,9):>12}   (c-1)/2={mp.nstr(mp.mpf(c-1)/2,9)}")
    print()

    # 4b: per-k full term vs -(1/2)(t tau)^2/(pi k)^2, then summed -> -1/24
    print("  4b) full per-k term (c=1,2) vs predicted -(1/2)(t tau)^2/(pi k)^2, and summed/tau -> -1/24:")
    for ts in ('0.02', '0.005'):
        tau = mp.mpf(ts)
        W = mp.sqrt(2 / tau)
        t = W / 2                         # saddle corner
        s = mp.mpc(0, t)
        print(f"    --- tau={ts},  saddle corner s=(0, W/2),  t={mp.nstr(t,6)} ---")
        print(f"      {'k':>4} | {'Re(k-term)':>16} | {'pred -(1/2)(t tau)^2/(pi k)^2':>30} | {'ratio':>8}")
        for k in (1, 2, 3, 5, 10):
            actual = kterm_re(s, tau, k)
            pred = -mp.mpf(1) / 2 * (t * tau) ** 2 / (mp.pi * k) ** 2
            ratio = actual / pred
            print(f"      {k:>4} | {mp.nstr(actual, 12):>16} | {mp.nstr(pred, 12):>30} | {mp.nstr(ratio,6):>8}")
        Kfull = 4000
        full = sum(kterm_re(s, tau, k) for k in range(1, Kfull + 1))
        print(f"      SUM over k=1..{Kfull}:  Re B(corner) = {mp.nstr(full, 12)}")
        print(f"          Re B / tau = {mp.nstr(full/tau, 10)}   (predicted -C = -1/24 = -0.0416667)")
        print()


def main():
    print("\n" + "#" * 78)
    print("#  lem:Bbounded  --  lower bound on Re B_s over strip S = {0<=Im s<=W/2, Re s>=0}")
    print("#  scalar mpmath, dps =", mp.mp.dps)
    print("#  VERDICT (see TASK 1): the correct bound is  Re B_s >= -C' sqrt(tau),  C'=sqrt2/18 ~0.0786,")
    print("#  NOT -C tau.  The -C tau form holds ONLY on the sigma=0 edge (C=1/24, TASK 4).")
    print("#" * 78 + "\n")
    # grid/scan tasks use K=2500 (tail per-k ~1/k^2; beyond 2500 is <1e-7, irrelevant to scaling).
    # K-stability (task0) independently confirms K>=4000 vs 8000 agreement.
    KG = 2500
    task0_kstability()
    task1_gridmin(K=KG)
    task1b_refine(K=KG)
    task2_monotone(K=KG)
    task3_resonance(K=KG)
    task4_perk()
    print("#" * 78)
    print("#  DONE")
    print("#" * 78)


if __name__ == "__main__":
    main()
