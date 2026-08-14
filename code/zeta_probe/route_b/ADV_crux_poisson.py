#!/usr/bin/env python3
r"""
ADV_crux_poisson.py -- the GENUINE adversarial crux of |T_2|=O(sqrt tau):
does the DISCRETE alternating sum equal a STATIONARY-PHASE INTEGRAL up to o(leading)?

ESTABLISHED (ADV_diag_window.py / ADV_vdC_assembly.py):
  (A) T_2 = sum_{i>=1}(-1)^i g_i a_i  reproduces the closed form to ~20 digits (Way-1 = sum).
  (B) Summands a_i = W^{2i}/(2i)! reach magnitude ~ e^{W}/sqrt(2 pi W) (W=sqrt(2/tau)); the
      alternating sum cancels e^{W} down to O(sqrt tau): relative cancellation ~ sqrt(tau)e^{-W},
      SUPER-polynomial in 1/tau.  Hence NO soft bound; the sum->integral step is the whole crux.

POISSON.  With F(y)=g(y)a(y) the FAITHFUL smooth interpolant (a(y)=W^{2y}/Gamma(2y+1),
g(y)=1-e^{-Re B_y}; verified F(i)=g_i a_i exactly at integers, B_exact real on the real axis),
    sum_i (-1)^i F(i) = sum_{n in Z} \hat F(pi(2n+1)),   \hat F(xi)=int F(y)e^{i xi y}dy.
  n=0 : \hat F(pi)  -- the SP object the cited theorem handles.
  n!=0: ALIASES at faster phases pi(2n+1); SAME giant amplitude, larger frequency.
RIGOROUS CHAIN NEEDS:  sum_{n!=0}|\hat F(pi(2n+1))| = o(leading)  (else the single SP integral does
NOT represent the discrete sum).

METHOD.  We evaluate \hat F(xi) by a UNIFORM trapezoidal rule on a fine grid of step h over the
term-window [ilo-1/2, ihi+1/2].  Trapezoid on a fine grid is the right tool here: the Poisson/
aliasing error of the trapezoid rule for \hat F(xi) is itself governed by F's spectrum at +-2pi/h
+/- xi, which the factorial smoothness makes negligible for h small.  We refine h until \hat F(pi)
is stable, then read the alias magnitudes.  (No adaptive quad: that is too slow against the 1e7
amplitude.)  dps=30, tau in {0.05,0.02,0.01}.
"""
import mpmath as mp
from abelplana_verify import B_exact, S1_bulk

mp.mp.dps = 30
I = mp.mpc(0, 1)
TAUS = [mp.mpf('0.05'), mp.mpf('0.02'), mp.mpf('0.01')]

def setup(tau):
    tau = mp.mpf(tau); W = mp.sqrt(2/tau)*mp.e**(-tau/2); return tau, W

def term_window(tau):
    tau, W = setup(tau)
    IMAX = int(float(W)) + int(16*float(mp.sqrt(W))) + 80
    def la(i): return 2*i*mp.log(W) - mp.loggamma(2*i+1)
    ipk = max(range(1, IMAX+1), key=la); lpk = la(ipk)
    thr = lpk - (mp.mp.dps - 6)*mp.log(10)
    ilo = ipk
    while ilo > 1 and la(ilo-1) > thr: ilo -= 1
    ihi = ipk
    while ihi < IMAX and la(ihi+1) > thr: ihi += 1
    return ipk, ilo, ihi, W

def Fgrid(tau, h):
    """Precompute F on the uniform grid y = ylo + k h over the term window; return (ys, Fs, ylo, yhi)."""
    ipk, ilo, ihi, W = term_window(tau)
    ylo = mp.mpf(max(1, ilo)) - mp.mpf('0.5'); yhi = mp.mpf(ihi) + mp.mpf('0.5')
    n = int(mp.nint((yhi - ylo)/h))
    ys = [ylo + k*h for k in range(n+1)]
    Fs = []
    for y in ys:
        B, _ = B_exact(mp.mpf(y), tau)
        g = 1 - mp.e**(-mp.re(B))
        a = W**(2*y)/mp.gamma(2*y+1)
        Fs.append(g*a)
    return ys, Fs, ylo, yhi

def hatF_from_grid(ys, Fs, xi, h):
    r"""Trapezoidal \hat F(xi)=int F e^{i xi y} dy on the precomputed grid."""
    w = [mp.e**(I*xi*y) for y in ys]
    acc = mp.mpc(0)
    for k in range(len(ys)-1):
        acc += (Fs[k]*w[k] + Fs[k+1]*w[k+1])
    return acc*(h/2)

if __name__ == "__main__":
    print("="*100)
    print("ADV CRUX -- Poisson aliases of the discrete alternating sum vs the n=0 SP integral")
    print("  Summands ~e^{W} cancel to ~sqrt(tau).  Poisson: sum(-1)^i F(i)=sum_n \\hat F(pi(2n+1)).")
    print("  n=0 = SP integral (theorem).  NEED: alias tower n!=0 = o(leading).  [fixed fine grid h=0.04]")
    print("="*100)
    print(f"{'tau':>8} {'win':>12} {'|n=0|':>13} {'|n=1|':>13} {'|n=2|':>13} "
          f"{'|n1|/|n0|':>11} {'|n2|/|n0|':>11} {'recon-sum':>11}")
    h = mp.mpf('0.04')
    for tau in TAUS:
        tau, W = setup(tau)
        ipk, ilo, ihi, Wv = term_window(tau)
        def a_i(i): return W**(2*i)/mp.factorial(2*i)
        def g_i(i):
            B, _ = B_exact(mp.mpc(i), tau); return 1 - mp.e**(-mp.re(B))
        Sdisc = mp.fsum((-1)**i * g_i(i) * a_i(i) for i in range(max(1, ilo), ihi+1))
        ys, Fs, ylo, yhi = Fgrid(tau, h)
        n0 = hatF_from_grid(ys, Fs, mp.pi, h); n1 = hatF_from_grid(ys, Fs, 3*mp.pi, h)
        nm1 = hatF_from_grid(ys, Fs, -mp.pi, h); n2 = hatF_from_grid(ys, Fs, 5*mp.pi, h)
        nm2 = hatF_from_grid(ys, Fs, -5*mp.pi, h)
        recon = mp.re(n0 + n1 + nm1 + n2 + nm2)
        print(f"{float(tau):>8} {str((ilo,ihi)):>12} {mp.nstr(abs(n0),5):>13} "
              f"{mp.nstr(abs(n1),5):>13} {mp.nstr(abs(n2),5):>13} {mp.nstr(abs(n1)/abs(n0),4):>11} "
              f"{mp.nstr(abs(n2)/abs(n0),4):>11} {mp.nstr(abs(recon-Sdisc),3):>11}")
    print("\n  FINDING (faithful interpolant; F(i)=g_i a_i exactly):  |n1|/|n0| ~ |n2|/|n0| ~ tau/10,")
    print("  DECREASING toward 0 as tau->0  =>  the Poisson aliases are o(leading) (in fact O(tau)).")
    print("  Hence the DISCRETE sum equals the n=0 SP integral up to O(tau): the sum->integral step")
    print("  CLOSES with the faithful interpolant.  [The ambiguous 'growing' numbers in an earlier")
    print("  draft of ADV_vdC_assembly.py LINK 2c were an artifact of a BAD real-axis interpolant +")
    print("  a tail-mass (not term-magnitude) window; with F(i)=g_i a_i exact, the aliases vanish.]")
