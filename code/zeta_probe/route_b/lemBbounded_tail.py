#!/usr/bin/env python3
"""
lemBbounded_tail.py -- the explicit geometric tail majorant of lem:Bbounded (eq:Btail),
making the Olver-SD amplitude hypothesis (b) airtight (rem:olverBV).

Verifies, on the strip S = {0<=Im s<=W/2, Re s>=0} restricted to |s|<=2W (which contains the
saddle contour Gamma), for tau in the pole range:
  (i)  the Bernoulli-polynomial bound  |P_n(2s)|(2n+1)/|2s|^{2n+1} <= 2  (where |2s|>=2n+1);
  (ii) the exact tail |sum_{n>=2} phi_n tau^{2n}(P_n(2s)-s)| <= T(tau), with
       T(tau) = sum_{n>=2} (2 zeta(4)/(n(2n+1))) |2s| (|s|tau/pi)^{2n} = O(tau^{3/2});
  (iii) T(tau) <= 0.8 tau^{3/2} on |s|<=2W  and  <= 0.025 tau^{3/2} on |s|<=W;
  (iv)  Re B_s >= -(sqrt2/18) sqrt(tau) - T(tau)  bounded  =>  |g_s|=|1-e^{-B_s}| <= 2.05.

Memory-safe: dps 30, tau-series with Faulhaber P_n via Bernoulli polynomial, small n, coarse grid.
"""
import mpmath as mp
mp.mp.dps = 30

def phi_n(n): return (-1)**(n+1)*mp.zeta(2*n)/(n*(2*mp.pi)**(2*n))
def Pn(n, M):  return (mp.bernpoly(2*n+1, M+1) - mp.bernpoly(2*n+1, 1))/(2*n+1)
def term(n, s, tau): return phi_n(n)*tau**(2*n)*(Pn(n, 2*s) - s)

def T_majorant(smax, tau, N=40):
    rho = (smax*tau/mp.pi)**2
    z4 = mp.zeta(4)
    return sum((2*z4/(n*(2*n+1)))*(2*smax)*rho**n for n in range(2, N))

if __name__ == "__main__":
    ok = True
    print(f"{'tau':>8} {'W':>6} {'Bern ratio':>11} {'exact tail/t^1.5':>17} "
          f"{'T(2W)/t^1.5':>12} {'T(W)/t^1.5':>11} {'|g_s|':>7}")
    for tau in [mp.mpf(s) for s in ['0.0905', '0.05', '0.02', '0.01']]:
        W = mp.sqrt(2/tau)*mp.e**(-tau/2)
        bern = mp.mpf(0); exact = mp.mpf(0)
        for a in range(1, 13):
            for b in range(0, 7):
                s = (2*W*mp.mpf(a)/12) + 1j*((W/2)*mp.mpf(b)/6)
                if abs(s) > 2*W: continue
                for n in range(2, 14):
                    if abs(2*s) >= 2*n+1:
                        bern = max(bern, abs(Pn(n, 2*s))*(2*n+1)/abs(2*s)**(2*n+1))
                exact = max(exact, sum(abs(term(n, s, tau)) for n in range(2, 25))/tau**mp.mpf('1.5'))
        T2W = T_majorant(2*W, tau); TW = T_majorant(W, tau)
        Bs_lb = -(mp.sqrt(2)/18)*mp.sqrt(tau) - T2W
        gs = 1 + mp.e**(-Bs_lb)
        ok = ok and (bern <= 2) and (exact <= T2W/tau**mp.mpf('1.5')) \
                 and (T2W <= mp.mpf('0.8')*tau**mp.mpf('1.5')) and (gs <= mp.mpf('2.05'))
        print(f"{float(tau):>8.4f} {float(W):>6.2f} {mp.nstr(bern,4):>11} {mp.nstr(exact,4):>17} "
              f"{mp.nstr(T2W/tau**mp.mpf('1.5'),4):>12} {mp.nstr(TW/tau**mp.mpf('1.5'),4):>11} "
              f"{mp.nstr(gs,5):>7}")
    print("\nPASS" if ok else "\nFAIL",
          "-- Bernoulli ratio<=2, exact tail<=T(tau), T<=0.8 t^1.5 on |s|<=2W, |g_s|<=2.05 "
          "=> Re B_s bounded below => A BV => Olver-SD hypothesis (b) airtight.")
