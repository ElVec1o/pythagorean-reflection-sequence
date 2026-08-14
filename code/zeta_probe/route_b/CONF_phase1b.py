"""
PHASE 1b: assemble log d_k in closed dilog form (both Pochhammers), VERIFY vs exact, locate the saddle.
  log d_k = i*pi*k + k*log(2(1-q)q^3) + k^2 log q - log(q^2;q^2)_k - log(q^5;q^2)_k
Pochhammer dilog reductions (q=e^{-tau}, EM/Bernoulli; (A) modular verified to 48 digits in phase1):
  log(q^2;q^2)_k = (1/(2tau))[Li2(z2) - pi^2/6] + (1/2)log(pi/(tau(1-z2))) + (tau/12)(1+z2)/(1-z2) + O(tau^2),  z2=q^{2k+2}
  log(q^5;q^2)_k = (1/(2tau))[Li2(z5) - C5] + (1/2)log( ? ) + ...    z5=q^{2k+5}   <- C5 and prefactor fit below.
We FIT the q^5 constant/prefactor numerically (same method), then assemble and verify.
"""
import mpmath as mp
mp.mp.dps = 40

def qpoch_k(a,q2,k):
    p=mp.mpf(1) if not isinstance(a,mp.mpc) else mp.mpc(1); aj=a
    for _ in range(k): p*=(1-aj); aj*=q2
    return p
def qpoch_inf(a,q2):
    p=mp.mpf(1) if not isinstance(a,mp.mpc) else mp.mpc(1); aj=a
    terms=int((mp.mp.dps+10)*2.3026/abs(mp.log(abs(q2))))+40
    for _ in range(terms):
        p*=(1-aj); aj*=q2
        if abs(aj)<mp.mpf(10)**(-(mp.mp.dps+8)): break
    return p

# ---- FIT the (q^5;q^2)_k reduction: log(q^5;q^2)_k - (1/(2tau))[Li2(z5)-pi^2/6] =? (1/2)log(pi*A/(tau(1-z5))) + ...
print("FIT (q^5;q^2)_k: resid = log(q^5;q^2)_k - (1/(2tau))[Li2(z5)-pi^2/6] - (1/2)log(pi/(tau(1-z5))) :")
for taus in ['0.02','0.01','0.005','0.002']:
    tau=mp.mpf(taus);q=mp.e**(-tau);q2=q*q;w=mp.sqrt(2/tau);k=int(mp.nint(w/2))
    z5=q**(2*k+5)
    exact=mp.log(qpoch_k(q**5,q2,k))
    lead=(1/(2*tau))*(mp.polylog(2,z5)-mp.pi**2/6)+mp.mpf('0.5')*mp.log(mp.pi/(tau*(1-z5)))
    resid=exact-lead
    print(f"  tau={taus:>6} k={k}: resid={mp.nstr(resid,10)}  resid-(tau/12)(1+z5)/(1-z5)={mp.nstr(resid-(tau/12)*(1+z5)/(1-z5),6)}  z5={mp.nstr(z5,5)}")

# The (q^5) Pochhammer starts at exponent 5 not 2, so the lower-end constant differs. Use the EXACT relation
#   (q^5;q^2)_inf = (q;q^2)_inf / ((1-q)(1-q^3)),  (q;q^2)_inf=(q;q)_inf/(q^2;q^2)_inf
# to get log(q^5;q^2)_inf rigorously, and the SAME tail dilog. Build it and verify the assembled log d_k:
def logd_dilog(k,tau):
    q=mp.e**(-tau);q2=q*q
    z2=q**(2*k+2); z5=q**(2*k+5)
    log2poch=(1/(2*tau))*(mp.polylog(2,z2)-mp.pi**2/6)+mp.mpf('0.5')*mp.log(mp.pi/(tau*(1-z2)))+(tau/12)*(1+z2)/(1-z2)
    # q^5 via exact inf + tail dilog:
    # log(q^5;q^2)_k = log(q^5;q^2)_inf - sum_{m>=k} log(1-q^{5+2m}); tail EM = -(1/(2tau))Li2(z5)+ (1/2)log(1-z5)+(tau/12)*...
    q_q   = qpoch_inf(q,q)       # (q;q)_inf
    q2q2  = qpoch_inf(q2,q2)     # (q^2;q^2)_inf
    log_q5_inf = mp.log(q_q) - mp.log(q2q2) - mp.log(1-q) - mp.log(1-q**3)  # (q^5;q^2)_inf=(q;q)/[(q^2;q^2)(1-q)(1-q^3)]
    tail = -(1/(2*tau))*mp.polylog(2,z5) + mp.mpf('0.5')*mp.log(1-z5) + (tau/12)*(1+z5)/(1-z5)
    log5poch = log_q5_inf - tail
    return mp.mpc(0,1)*mp.pi*k + k*mp.log(2*(1-q)*q**3) + k*k*mp.log(q) - log2poch - log5poch

print("\nVERIFY assembled log d_k (dilog) vs exact, at saddle-scale k (real k):")
for taus in ['0.02','0.01','0.005']:
    tau=mp.mpf(taus);q=mp.e**(-tau);q2=q*q;w=mp.sqrt(2/tau);k=int(mp.nint(w/2))
    dk_exact=((-2)**k)*((1-q)**k)*q**(k*k+3*k)/(qpoch_k(q2,q2,k)*qpoch_k(q**5,q2,k))
    log_exact=mp.log(abs(dk_exact))+mp.mpc(0,1)*(mp.pi*k if dk_exact<0 else 0)  # sign->i pi k mod 2pi
    appx=logd_dilog(k,tau)
    print(f"  tau={taus:>6} k={k}: Re exact={mp.nstr(mp.log(abs(dk_exact)),12)}  Re dilog={mp.nstr(mp.re(appx),12)}  diff={mp.nstr(mp.re(appx)-mp.log(abs(dk_exact)),4)}")
