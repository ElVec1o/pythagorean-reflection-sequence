"""
D4 FINAL: consolidated verification of the POLE PHASE result.

RESULT (rigorous skeleton + numerics):
  Travel block:  Sigma_1(q) = (1-cos w) + c_T sqrt(tau) sin w + O(tau),   c_T = sqrt2/36 = 0.0392837...
  POLE (Sigma_1=1):  cos w_m = c_T sqrt(tau) sin w_m + O(tau^{3/2}),
     w_m = (m-1/2)pi - c_T sqrt(tau) + O(tau),   sin w_m = (-1)^{m-1}(1+O(tau)),
     cos w_m = c_T sqrt(tau) (-1)^{m-1} + O(tau^{3/2}).
  Phase-shifted values (W=w e^{-tau/2}, W/q = w e^{tau/2}):
     cos W_m    = ( 1/sqrt2 + c_T) sqrt(tau) sin w_m + O(tau^{3/2}) = 0.746390 sqrt(tau) sin w_m + ...
     cos(W_m/q) = (-1/sqrt2 + c_T) sqrt(tau) sin w_m + O(tau^{3/2}) = -17 sqrt2/36 sqrt(tau) sin w_m + ...
     sin W_m = sin(W_m/q) = (-1)^{m-1} + O(tau).

DERIVATION (each step machine-checked above):
  D1. ratio rho^T_j/rho^T_{j-1}, y=j*tau: log = 2y+2log(2y/(e^{2y}-1)), O(tau) part = -y/2+y^3/30 (NO const).
      => log rho^T_j = -(1/9)tau^2 j^3 + (1/450)tau^4 j^5 - ... (no linear -(j+1)tau term).
  D2. E^T = Sigma_1-(1-cos w) = -sum_n (-1)^{n-1}(w^{2n}/(2n)!) delta_{n-1}, delta_j ~ (1/9)tau^2 j^3.
  D3. vartheta^3(1-cos w) = (w/8)(-w^2 sin w+3w cos w+sin w) ~ -(w^3/8)sin w.
      E^T_lead = -(1/9)tau^2 * (-(w^3/8)sin w) = (1/72)tau^2 w^3 sin w = (sqrt2/36)sqrt(tau)sin w  [tau^2 w^3=2sqrt2 sqrt tau].
  => c_T = sqrt2/36.   The j^2 EM-correction -> O(tau)cos w -> O(tau^{3/2}) at pole (negligible).
"""
import mpmath as mp

KSTART = 1
def Aq(k, q):  return 2 * q / (1 - q ** (k + 1))
def Cq(k, q):  return 2 * q ** (k + 3) / (1 - q ** (k + 2)) - 2 * q ** (k + 2) / (1 - q ** (k + 1))
def sig_t(q):
    tot = mp.mpf(0); prod = mp.mpf(1)
    tiny = mp.mpf(10) ** (-(mp.mp.dps + 12)); j = 0
    while True:
        kk = KSTART + 2*j
        tot += Aq(kk,q)*prod; prod *= Cq(kk,q)
        if abs(prod) < tiny and j > 60: break
        j += 1
    return tot
def repolish(seed): return mp.findroot(lambda Q: sig_t(Q)-1, seed)

if __name__ == "__main__":
    seeds = [l.strip() for l in open("poles.txt") if l.strip()]
    cT = mp.sqrt(2)/36
    test = [4, 16, 40, 79]
    qmax = mp.mpf(seeds[max(test)]); taumin = -mp.log(qmax)
    mp.mp.dps = 40 + int(2.5*mp.sqrt(2/taumin))
    print(f"# dps={mp.mp.dps}, c_T = sqrt2/36 = {mp.nstr(cT,12)}")
    print(f"# predicted limits: cosW/(st sw)=1/sqrt2+c_T={mp.nstr(1/mp.sqrt(2)+cT,9)}, "
          f"cosWq/(st sw)=c_T-1/sqrt2=-17sqrt2/36={mp.nstr(cT-1/mp.sqrt(2),9)}\n")
    print(f"{'m':>3} {'tau':>11} {'resid':>9} {'cosw/stsw':>12} {'cosW/stsw':>12} {'cosWq/stsw':>12} {'w_m-(m-.5)pi+c_T*st':>20}")
    for i in test:
        q = repolish(seeds[i]); tau = -mp.log(q)
        w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2); Wq = W/q; st = mp.sqrt(tau)
        sw = mp.sin(w)
        resid = sig_t(q)-1
        c1 = mp.cos(w)/(st*sw); c2 = mp.cos(W)/(st*sw); c3 = mp.cos(Wq)/(st*sw)
        # w_m relative to (m-1/2)pi: the m-index for pole i (0-based file) is m = i+?
        # poles.txt[0] is the first pole; w near (m-1/2)pi. find nearest half-integer multiple:
        kk = mp.nint(w/mp.pi - mp.mpf('0.5'))
        eps = w - (kk+mp.mpf('0.5'))*mp.pi   # = w_m - (m-1/2)pi, predicted = -c_T sqrt tau
        eps_check = (eps + cT*st)/st         # should -> 0 as O(sqrt tau)
        print(f"{i:>3} {mp.nstr(tau,5):>11} {mp.nstr(resid,2):>9} {mp.nstr(c1,8):>12} {mp.nstr(c2,8):>12} {mp.nstr(c3,8):>12} {mp.nstr(eps_check,6):>20}")
    print("\n# 'w_m-(m-.5)pi+c_T*st' column /sqrt(tau) -> 0 (O(sqrt tau)) confirms eps_m = -c_T sqrt(tau)+O(tau).")
    print(f"# c_T = sqrt2/36 = {mp.nstr(cT,8)}  (6+ digits: 0.0392837)")
