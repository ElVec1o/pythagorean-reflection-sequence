import mpmath as mp
mp.mp.dps = 45
# Decisive uniformity test: is the q-Bessel/classical AMPLITUDE correction O(tau) and x-INDEPENDENT?
# Evaluate (J3/J_cl - 1)/tau at many arguments A (away from classical zeros) at FIXED tau.
# Modular-theta prediction: x-INDEPENDENT (the e^{(eps/2)3nu(nu+1)} factor doesn't depend on A) => flat.
# Naive term-by-term prediction: grows ~A^2.  The flat-vs-growing outcome decides uniformity.
def qpoch(a,q,n):
    r=mp.mpf(1)
    for k in range(n): r*=(1-a*q**k)
    return r
def qpoch_inf(a,q):
    r=mp.mpf(1); k=0
    while True:
        t=1-a*q**k
        r*=t; k+=1
        if abs(t-1)<mp.mpf(10)**(-44) or k>400000: break
    return r
def J3(nu,x,q,N=300):
    pref=qpoch_inf(q**(nu+1),q)/qpoch_inf(q,q)
    s=mp.fsum((-1)**n*q**(mp.mpf(n*(n-1))/2)*(q*x*x)**n/(qpoch(q**(nu+1),q,n)*qpoch(q,q,n)) for n in range(N))
    return pref*x**nu*s
nu=mp.mpf(3)/2
# classical J_{3/2} zeros near 4.49, 7.725, 10.904, 14.066 -> avoid
zeros=[4.493,7.725,10.904,14.066]
print(f"{'A':>5} {'(J3/Jcl - 1)/tau':>22}   note   (tau=0.004)")
tau=mp.mpf('0.004'); q=mp.e**(-tau)
for Af in [5,6,7,8.5,9,10,12,13,15,16,18,20]:
    A=mp.mpf(Af)
    near = min(abs(A-z) for z in zeros)
    x=A*(1-q)/2
    cls=mp.besselj(nu,A)
    val=J3(nu,x,q)
    coef=(val/cls-1)/tau
    flag = "  <-- near zero (noisy)" if near<0.6 else ""
    print(f"{Af:>5} {mp.nstr(coef,12):>22}{flag}")
print()
print("If the column is ~FLAT (bounded, ~const) as A grows: amplitude correction is x-independent O(tau)")
print(" => the bound R=O(tau^{5/2}) holds UNIFORMLY in the pole index. (Matches the modular-theta mechanism.)")
print("If it GROWS like A^2: the naive expansion wins and uniformity fails.")
