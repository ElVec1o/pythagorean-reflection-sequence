"""
D4 step 4: Verify the analytic derivation of c_T = sqrt2/36 for the TRAVEL block.

DERIVATION (rigorous skeleton):
  Travel form factor rho^T_j = t^T_j/hat t_j has, in the saddle window j=O(tau^{-1/2}),
      log rho^T_j = -(1/9) tau^2 j^3 + (1/450) tau^4 j^5 - ...     (NO linear -(j+1)tau term!)
  [from log(rho_j/rho_{j-1}) = 2y+2log(2y/(e^{2y}-1)), y=j*tau, integrated: -y^3/9+y^5/450-...]
  vs BULK S_1:  log rho^bulk_j = -(j+1)tau - (1/9)tau^2 j^3 + ...   (HAS the linear term).

  Then  E^T := Sigma_1 - (1-cos w) = -sum_{n>=1}(-1)^{n-1}(w^{2n}/(2n)!) delta^T_{n-1},
  delta^T_j = 1-rho^T_j ~ (1/9)tau^2 j^3.  The cubic term resums via vartheta^3:
      sum_n (-1)^{n-1} n^3 w^{2n}/(2n)! = vartheta^3(1-cos w) = (w/8)(-w^2 sin w + 3w cos w + sin w)
                                        ~ -(w^3/8) sin w   (leading).
  E^T_lead = -(1/9)tau^2 * (-(w^3/8) sin w) = (1/72) tau^2 w^3 sin w.
  With tau^2 w^3 = 2 sqrt2 sqrt(tau):   E^T_lead = (2 sqrt2/72) sqrt(tau) sin w = (sqrt2/36) sqrt(tau) sin w.
  => c_T = +sqrt2/36 = 0.0392837100...

  Hence at a pole (Sigma_1=1): 0 = 1 - [ (1-cos w_m) + c_T sqrt(tau) sin w_m + O(tau) ]
       =>  cos w_m = c_T sqrt(tau) sin w_m + O(tau),   c_T = sqrt2/36.

This script:
  (A) confirms log(rho_j/rho_{j-1}) = 2y+2log(2y/(e^{2y}-1)) at fixed y=j*tau (no linear-tau term),
  (B) confirms (Sigma_1-(1-cos w))/(sqrt(tau) sin w) -> sqrt2/36 by Richardson over tau, sin w=1 phase,
  (C) confirms the bulk S_1 -> -17 sqrt2/36 by the same machinery (sanity).
"""
import mpmath as mp

KSTART = 1
def Aq(k, q):  return 2 * q / (1 - q ** (k + 1))
def Cq(k, q):  return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))
def alpha(k, q): return 2 / (q**(-(k+1)) - 1)
def gamma(k, q): return alpha(k+1, q) - alpha(k, q)

def sigma1_travel(q, J=4000000):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12))
    for j in range(J):
        kk = KSTART + 2 * j
        tot += Aq(kk, q) * prod; prod *= Cq(kk, q)
        if abs(prod) < tiny and j > 60: break
    return tot

def S1_bulk(q, J=4000000):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12))
    for j in range(J):
        kk = 1 + 2 * j
        tot += alpha(kk, q) * prod; prod *= gamma(kk, q)
        if abs(prod) < tiny and j > 60: break
    return tot

def hat_t(j, tau): return (2 / tau) ** (j + 1) / mp.factorial(2 * j + 2)

if __name__ == "__main__":
    mp.mp.dps = 120

    print("=== (A) log(rho_j/rho_{j-1}) = 2y + 2 log(2y/(e^{2y}-1)),  y=j*tau (travel) ===")
    tau = mp.mpf('0.0008')
    q = mp.e ** (-tau)
    # build rho_j from terms
    J = 200
    ts = []; prod = mp.mpf(1)
    for j in range(J):
        kk = KSTART + 2*j; ts.append(Aq(kk,q)*prod); prod *= -Cq(kk,q)
    rho = [ts[j]/hat_t(j,tau) for j in range(J)]
    print(f"{'j':>4} {'y=jtau':>10} {'log(rho_j/rho_{j-1}) actual':>26} {'predicted 2y+2log(2y/(e2y-1))':>30} {'diff':>10}")
    for j in [5,10,20,40,60]:
        y = j*tau
        actual = mp.log(rho[j]/rho[j-1])
        pred = 2*y + 2*mp.log(2*y/(mp.e**(2*y)-1))
        print(f"{j:>4} {mp.nstr(y,5):>10} {mp.nstr(actual,12):>26} {mp.nstr(pred,12):>30} {mp.nstr(actual-pred,3):>10}")

    print("\n=== (B) Richardson: (Sigma_1-(1-cos w))/(sqrt(tau) sin w) -> c_T at sin w = 1 ===")
    cT_target = mp.sqrt(2)/36
    # pick tau so that w=sqrt(2/tau) hits sin w = 1, i.e. w = (2N+0.5)pi  => tau = 2/w^2
    vals = []
    taus = []
    for N in [40, 80, 160, 320, 640]:
        w = (2*N + mp.mpf('0.5'))*mp.pi   # sin w = 1
        tau = 2/w**2
        q = mp.e**(-tau)
        s1 = sigma1_travel(q)
        E = s1 - (1 - mp.cos(w))
        val = E/(mp.sqrt(tau)*mp.sin(w))   # sin w = 1
        vals.append(val); taus.append(tau)
        print(f"  N={N:4d} tau={mp.nstr(tau,5)} w={mp.nstr(w,8)} sinw={mp.nstr(mp.sin(w),4)} (E)/(sqrt(tau))={mp.nstr(val,12)}")
    # Richardson extrapolate in sqrt(tau): val = cT + a*sqrt(tau) + ...
    print(f"  -> last value {mp.nstr(vals[-1],10)},  c_T target sqrt2/36 = {mp.nstr(cT_target,10)}")
    # simple Richardson assuming val ~ cT + a*sqrt(tau): each tau halves w^2 => sqrt(tau) /2
    r = mp.sqrt(taus[-2]/taus[-1])  # ratio of sqrt(tau)
    extrap = (vals[-1]*r - vals[-2])/(r-1)   # eliminate linear-in-sqrt-tau
    print(f"  Richardson (1-step, linear in sqrt tau) extrap = {mp.nstr(extrap,10)}  vs sqrt2/36={mp.nstr(cT_target,10)}")

    print("\n=== (C) SANITY bulk S_1 -> -17 sqrt2/36 (same machinery, has linear term) ===")
    c1_bulk = -17*mp.sqrt(2)/36
    for N in [80, 320]:
        w = (2*N + mp.mpf('0.5'))*mp.pi
        tau = 2/w**2; q = mp.e**(-tau)
        s1 = S1_bulk(q)
        E = s1 - (1 - mp.cos(w))
        val = E/(mp.sqrt(tau)*mp.sin(w))
        print(f"  N={N} (S1-(1-cos w))/sqrt(tau) = {mp.nstr(val,10)}  target -17sqrt2/36={mp.nstr(c1_bulk,10)}")
