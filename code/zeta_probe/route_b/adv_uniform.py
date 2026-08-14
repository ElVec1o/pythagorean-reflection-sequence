#!/usr/bin/env python3
"""
CRITICAL adversarial test: what does 'uniform in w' MEAN, and does T2 = O(sqrt tau)
hold uniformly?

T2(W, tau) = sum_{i>=1} (-1)^i [W^{2i}/(2i)!] g_i,  g_i = 1-e^{-B_i(tau)}.
B_i depends ONLY on tau. W appears only via a_i.

In the application W = w e^{-tau/2}, w = sqrt(2/tau), so W ~ sqrt(2/tau) is TIED to tau.
The colleague claims uniformity 'in w'. We test three readings:

(1) ON-SHELL: W = sqrt(2/tau) e^{-tau/2}.  T2 is a function of tau alone.
    (Already scanned: sup |T2|/sqrt(tau) ~ 0.0525.)

(2) W treated as FREE >> sqrt(2/tau): is T2/sqrt(tau) still bounded? (Should BLOW UP if
    the sqrt(tau) really comes from the on-shell relation W^2 ~ 2/tau.)

(3) The genuine 'uniform in w' from the lemma: the oscillation cos w as q varies. Since
    a tiny change in tau changes w=sqrt(2/tau) hugely, scanning tau densely already
    samples ALL phases. So (1) at fine tau-resolution IS the uniformity test.
"""
import mpmath as mp
from adv_verify import B_int

def T2_of_W_tau(W, tau, N=None):
    W = mp.mpf(W); tau = mp.mpf(tau)
    if N is None:
        N = int(3*float(W)) + 40
    # precompute integer B_i
    tot = mp.mpf(0)
    for i in range(1, N+1):
        Bi = B_int(i, tau)
        gi = 1 - mp.e**(-Bi)
        ai = W**(2*i)/mp.factorial(2*i)
        tot += (-1)**i * ai * gi
    return tot

if __name__ == "__main__":
    mp.mp.dps = 120
    print("="*92)
    print("(2) W treated as FREE (decoupled from tau). Fix tau, scan W. Does |T2|/sqrt(tau) blow up?")
    print("="*92)
    for tau in [mp.mpf('0.01'), mp.mpf('0.001')]:
        Won = mp.sqrt(2/tau)*mp.e**(-tau/2)
        print(f"\n  tau={float(tau)}  on-shell W={float(Won):.4f}")
        for fac in [mp.mpf('0.5'), mp.mpf('1'), mp.mpf('1.5'), mp.mpf('2'), mp.mpf('3'), mp.mpf('5')]:
            W = Won*fac
            t2 = T2_of_W_tau(W, tau)
            print(f"    W={float(W):9.3f} (={float(fac)}x on-shell)  "
                  f"|T2|={mp.nstr(abs(t2),6):>14}  |T2|/sqrt(tau)={mp.nstr(abs(t2)/mp.sqrt(tau),6)}")

    print("\n" + "="*92)
    print("(3) UNIFORM-IN-PHASE: ultra-fine tau scan near tau=0.25 and near tau=0.0005,")
    print("    sampling the cos w oscillation. sup |T2|/sqrt(tau).")
    print("="*92)
    from adv_verify import T2_direct
    for center, npts, span in [(mp.mpf('0.25'), 60, mp.mpf('0.04')),
                                (mp.mpf('0.0005'), 80, mp.mpf('0.0002'))]:
        sup = mp.mpf(0); args=None
        lo = center-span; hi=center+span
        for j in range(npts):
            tau = lo + (hi-lo)*j/(npts-1)
            r = abs(T2_direct(tau))/mp.sqrt(tau)
            if r>sup: sup=r; args=float(tau)
        print(f"  near tau={float(center)} (span {float(span)}, {npts} pts): "
              f"sup |T2|/sqrt(tau)={mp.nstr(sup,8)} at tau={args}")
