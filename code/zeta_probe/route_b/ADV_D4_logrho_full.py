"""
ADVERSARIAL: does the dropped tau^1 per-step term (and Euler-Maclaurin) corrupt the LEADING c_T,
or only the subleading remainder?

Strategy: c_T comes from  E^T = Sig_t - (1-cos w) = -sum_{j} (delta_j)(-1)^j hat_t_j-ish ... actually
  Sig_t = sum_j t_j = sum_j (-1)^j hat_t_j rho_j = sum_j (-1)^j hat_t_j (1 - delta_j),
  delta_j = 1 - rho_j.
  => Sig_t = (1-cos w) - sum_j (-1)^j hat_t_j delta_j.
  => E^T := Sig_t-(1-cos w) = - sum_j (-1)^j hat_t_j delta_j.
With (-1)^j hat_t_j = (-1)^j (2/tau)^{j+1}/(2j+2)! and delta_j ~ (1/9)tau^2 j^3 (LEADING),
the n=j+1 reindexing turns sum_j (-1)^j hat_t_j j^3 into a vartheta^3 acting on (1-cos w).

The c_T-determining quantity is the COEFFICIENT of the j^3 piece of delta_j, = -(1/9)tau^2 (from -log rho_j
leading = (1/9)tau^2 j^3, and delta_j = 1-rho_j = -(log rho_j) - (log rho_j)^2/2 - ... = (1/9)tau^2 j^3 + O(...)).

TEST 1: Does delta_j's LEADING j^3-coefficient equal exactly (1/9)tau^2, INDEPENDENT of the tau^1
per-step term?  The tau^1 per-step term integrates to an O(tau)*j^2-type contribution to log rho_j
(one power of tau higher and one power of j lower than the cubic), so it CANNOT change the tau^2 j^3
coefficient.  Verify: fit log rho_j = a*j^3 + (corrections) and check a -> -(1/9)tau^2.

TEST 2: Reconstruct E^T directly from the ACTUAL delta_j (no model for delta), and from delta_j^{lead}=(1/9)tau^2 j^3,
and confirm both give E^T/(sqrt tau sin w) -> c_T, with the difference O(tau) (subleading).
"""
import mpmath as mp

def Aq(k, q): return 2*q/(1 - q**(k+1))
def Cq(k, q): return 2*q**(k+3)/(1 - q**(k+2)) - 2*q**(k+2)/(1 - q**(k+1))

def build(tau, J):
    q = mp.e**(-tau)
    t=[]; prod=mp.mpf(1)
    for jj in range(J):
        kk=1+2*jj; t.append(Aq(kk,q)*prod); prod*=Cq(kk,q)
    return q,t

if __name__=="__main__":
    print("TEST 1: leading j^3 coefficient of log rho_j -> -(1/9) tau^2 ?")
    for tau in [mp.mpf('0.002'), mp.mpf('0.0008'), mp.mpf('0.0002')]:
        mp.mp.dps = 80 + int(2.5*mp.sqrt(2/tau))
        w = mp.sqrt(2/tau)
        J = int(3*w)+50
        q,t = build(tau,J)
        def hat(jj): return (2/tau)**(jj+1)/mp.factorial(2*jj+2)
        # log rho_j at a moderate j well inside saddle window but small y
        # extract a = log rho_j / j^3 limit as j fixed small fraction of saddle, then *9/tau^2
        rows=[]
        for jj in [8,12,16,20]:
            rho = t[jj]/((-1)**jj*hat(jj))
            lr = mp.log(rho)
            a = lr/jj**3
            rows.append(a*9/tau**2)   # should -> -1
        print(f"  tau={mp.nstr(tau,4)}: (logrho/j^3)*9/tau^2 at j=8,12,16,20 = "
              + ", ".join(mp.nstr(r,8) for r in rows) + "  (target -1)")

    print("\nTEST 2: E^T from ACTUAL delta_j vs delta_j^lead=(1/9)tau^2 j^3, at sin w=1 phases.")
    cT = mp.sqrt(2)/36
    for N in [80,160,320]:
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2
        mp.mp.dps = 60+int(float(w)/mp.log(10))+30
        w=(2*N+mp.mpf('0.5'))*mp.pi; tau=2/w**2
        q=mp.e**(-tau)
        J=int(3*w)+80
        _,t=build(tau,J)
        def hat(jj): return (2/tau)**(jj+1)/mp.factorial(2*jj+2)
        # E^T = - sum_j (-1)^j hat_j delta_j, delta_j = 1 - rho_j, rho_j = t_j/((-1)^j hat_j)
        # = -sum_j [ (-1)^j hat_j - t_j ] = -[ (1-cos w) - Sig_t ] = Sig_t - (1-cos w).  (consistency)
        Sig = mp.fsum(t)
        E_actual = Sig - (1-mp.cos(w))
        # model E from delta_lead: E_lead = - sum_j (-1)^j hat_j * (1/9)tau^2 j^3
        E_lead = -mp.fsum([(-1)**jj*hat(jj)*(mp.mpf(1)/9*tau**2*jj**3) for jj in range(J)])
        va = E_actual/(mp.sqrt(tau))   # sin w=1
        vl = E_lead/(mp.sqrt(tau))
        print(f"  N={N}: E_actual/sqrt(tau)={mp.nstr(va,12)}  E_lead/sqrt(tau)={mp.nstr(vl,12)}  "
              f"both vs cT={mp.nstr(cT,10)}; diff(actual-lead)={mp.nstr(va-vl,5)}")
