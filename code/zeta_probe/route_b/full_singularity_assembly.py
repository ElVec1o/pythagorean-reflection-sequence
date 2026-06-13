import mpmath as mp
mp.mp.dps=40
# 1) Confirm the k-sum is the travel transfer criticality (no separate smaller pole).
#    The geometric k-sum pole IS Sigma_1^T=1 (each travel edge is one unit of the run;
#    summing over k = summing the run length = the resolvent (1-Sigma_1)^{-1}). So the
#    "geometric-sum pole" and the "1-Sigma=0 root" COINCIDE: rho is the unique object.
# 2) Confirm bulk resolvent finite at travel q*: Sigma_1^bulk(q*_travel) < 1 ?
def Aq(k,q): return 2*q/(1-q**(k+1))   # travel
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig_t(k,q,J=3000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-50) and j>40: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))   # bulk
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sig_b(k,q,J=3000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-50) and j>40: break
    return tot
qstar=mp.findroot(lambda q: Sig_t(1,q)-1, mp.mpf('0.4494536305589'))
print("q*_travel        =", mp.nstr(qstar,25))
print("Sigma_1^bulk(q*) =", mp.nstr(Sig_b(1,qstar),12), " (<1 => bulk resolvent FINITE here, no pole)")
print("=> bulk end-dressing = finite factor; dominant singularity rho = travel pole.")
print()
print("rho (x) =", mp.nstr(mp.sqrt(qstar),25))
print("beta_2_relaxed = 1/rho =", mp.nstr(1/mp.sqrt(qstar),25))
print()
# sanity: bulk pole rate
qb=mp.findroot(lambda q: Sig_b(1,q)-1, mp.mpf('0.6095'))
print("(bulk pole q*=%s rate=%s -- subdominant, matches seed)"%(mp.nstr(qb,16),mp.nstr(1/mp.sqrt(qb),12)))
