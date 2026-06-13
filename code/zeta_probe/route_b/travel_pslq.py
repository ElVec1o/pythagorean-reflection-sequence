import mpmath as mp
mp.mp.dps=120
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=4000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod
        prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-130) and j>40: break
    return tot
qstar=mp.findroot(lambda q: Sigma(1,q)-1, mp.mpf('0.4494536305589480461'))
beta=1/mp.sqrt(qstar)
print("q*      =", mp.nstr(qstar,60))
print("beta_2  =", mp.nstr(beta,60))
print("1/q*    =", mp.nstr(1/qstar,40))

# PSLQ on powers of q* (test algebraicity deg<=6)
def pslq_powers(val, deg, name, maxcoeff=10**8):
    vec=[val**i for i in range(deg+1)]
    rel=mp.pslq(vec, maxcoeff=maxcoeff, maxsteps=100000)
    print(f"  PSLQ {name} deg<={deg}: {rel}")
    if rel:
        h=max(abs(c) for c in rel)
        print(f"     max|coeff|={h}")
print("\n--- q* algebraicity ---")
for d in [2,3,4,5,6]: pslq_powers(qstar,d,"q*")
print("\n--- beta_2 algebraicity ---")
for d in [2,3,4,5,6]: pslq_powers(beta,d,"beta")
print("\n--- check simple closed forms ---")
print("  3/2 =",mp.nstr(mp.mpf(3)/2,10),"  beta-3/2=",mp.nstr(beta-mp.mpf(3)/2,6))
print("  sqrt(2)=",mp.nstr(mp.sqrt(2),10)," beta-sqrt2=",mp.nstr(beta-mp.sqrt(2),6))
print("  q*-9/20=",mp.nstr(qstar-mp.mpf(9)/20,6))
