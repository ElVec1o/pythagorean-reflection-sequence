"""
PHASE 1 of the confluence grind: rigorous Euler-Maclaurin/dilog reduction of the q-Pochhammers,
the backbone for a steepest-descent of Y3(1)=sum_k d_k with EXPLICIT error.

d_k = (-2)^k (1-q)^k q^{k^2+3k} / [(q^2;q^2)_k (q^5;q^2)_k],  q=e^{-tau}.

Claim (to verify numerically, then the EM remainder makes it rigorous):
  (A) MODULAR:  log(q^2;q^2)_inf = -pi^2/(12 tau) + (1/2)log(pi/tau) + tau/12 + O(tau^3)   [q=e^{-tau}, eta-asymptotic]
  (B) TAIL via EM:  sum_{m>=k+1} log(1-q^{2m}) = -(1/(2tau)) Li2(q^{2k+2}) + (1/2)log(1-q^{2k+2})
                     - (tau/6) * [q^{2k+2}/(1-q^{2k+2})] + ...   (Bernoulli)
  (C) => log(q^2;q^2)_k = (A) - (B), i.e.
        log(q^2;q^2)_k = (1/(2tau))[Li2(q^{2k+2}) - pi^2/6] + (1/2)log(pi/(tau(1-q^{2k+2}))) + (EM corr) + ...
  Analogously for (q^5;q^2)_k with lower limit shifted (m: 5,7,...).
We VERIFY (A),(B),(C) to many digits and extract the O(tau) Bernoulli correction so it is pinned, not guessed.
"""
import mpmath as mp
mp.mp.dps = 50

def qpoch_k(a, q2, k):
    """(a;q2)_k = prod_{j=0}^{k-1}(1-a q2^j)."""
    p = mp.mpf(1); aj = a
    for _ in range(k):
        p *= (1 - aj); aj *= q2
    return p

def qpoch_inf(a, q2):
    p = mp.mpf(1); aj = a; terms = int((mp.mp.dps+10)*2.3026/abs(mp.log(q2)))+40
    for _ in range(terms):
        p *= (1 - aj); aj *= q2
        if abs(aj) < mp.mpf(10)**(-(mp.mp.dps+8)): break
    return p

print("="*84)
print("PHASE 1: verifying the EM/dilog reduction of log(q^2;q^2)_k  (q=e^{-tau})")
print("="*84)

# --- (A) modular asymptotic of (q^2;q^2)_inf ---
print("\n(A) log(q^2;q^2)_inf vs  -pi^2/(12 tau) + (1/2)log(pi/tau) + tau/12 :")
for taus in ['0.05','0.02','0.01','0.005']:
    tau = mp.mpf(taus); q = mp.e**(-tau); q2 = q*q
    exact = mp.log(qpoch_inf(q2, q2))
    approx = -mp.pi**2/(12*tau) + mp.mpf('0.5')*mp.log(mp.pi/tau) + tau/12
    print(f"  tau={taus:>6}: exact={mp.nstr(exact,16)}  approx={mp.nstr(approx,16)}  diff={mp.nstr(exact-approx,3)}")

# --- (C) full claim for log(q^2;q^2)_k at the saddle-scale k ~ w/2 ---
print("\n(C) log(q^2;q^2)_k - [ (1/(2tau))(Li2(q^{2k+2})-pi^2/6) + (1/2)log(pi/(tau(1-q^{2k+2}))) ]  (-> EM corr):")
print("    (k chosen ~ w/2 = 1/sqrt(2 tau), the saddle scale)")
for taus in ['0.02','0.01','0.005','0.002']:
    tau = mp.mpf(taus); q = mp.e**(-tau); q2 = q*q; w = mp.sqrt(2/tau)
    k = int(mp.nint(w/2))
    exact = mp.log(qpoch_k(q2, q2, k))
    z = q**(2*k+2)
    lead = (1/(2*tau))*(mp.polylog(2, z) - mp.pi**2/6) + mp.mpf('0.5')*mp.log(mp.pi/(tau*(1-z)))
    corr = exact - lead
    # candidate EM O(tau) term: -(tau/12)*(d/dk stuff) ~ -(tau/6) z/(1-z)?  print corr and corr/tau
    print(f"  tau={taus:>6} k={k:>3}: corr={mp.nstr(corr,12)}  corr/tau={mp.nstr(corr/tau,8)}  z={mp.nstr(z,6)}")

# --- identify the O(tau) correction term structurally ---
print("\n    Identify corr: test corr ?= -(tau/12)[2/(1-z) - 1]*(something).  Print corr, and a few candidates:")
for taus in ['0.01','0.005','0.002']:
    tau = mp.mpf(taus); q = mp.e**(-tau); q2 = q*q; w = mp.sqrt(2/tau)
    k = int(mp.nint(w/2)); exact = mp.log(qpoch_k(q2,q2,k)); z = q**(2*k+2)
    lead = (1/(2*tau))*(mp.polylog(2,z)-mp.pi**2/6) + mp.mpf('0.5')*mp.log(mp.pi/(tau*(1-z)))
    corr = exact - lead
    c1 = -(tau/12)*(z/(1-z))           # candidate A
    c2 = -(tau/12)*(1+z)/(1-z)         # candidate B (EM f'(k+1) ~ derivative of log(1-q^{2m}))
    c3 = (tau/12)                      # constant
    print(f"  tau={taus:>6}: corr={mp.nstr(corr,8)}  candA={mp.nstr(c1,8)}  candB={mp.nstr(c2,8)}  tau/12={mp.nstr(c3,8)}")
