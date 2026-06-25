import mpmath as mp
mp.mp.dps = 40
def qpoch(a, base, n):
    pr = mp.mpf(1); ai = mp.mpf(1)*a
    for i in range(n):
        pr *= (1 - ai); ai *= base
    return pr
def u_k(k, tau):
    q = mp.e**(-tau); p = q*q
    num = 2*q * (-2*(1-q))**k * q**(k*k + 2*k)
    den = qpoch(p, p, k+1) * qpoch(q*p, p, k)
    return num/den

# Analytic small-tau limit of u_k:  as tau->0, q->1.
#  num = 2 q (-2(1-q))^k q^{k^2+2k} -> 2 (-2 tau)^k  (since 1-q ~ tau, q->1)
#  (q^2;q^2)_{k+1} = prod_{i=0}^{k}(1-q^{2(i+1)}) ~ prod_{i=1}^{k+1}(2 i tau) = (2tau)^{k+1}(k+1)!
#  (q^3;q^2)_k = prod_{i=0}^{k-1}(1-q^{3+2i}) ~ prod (3+2i)tau = tau^k * prod_{i=0}^{k-1}(3+2i) = tau^k (2k+1)!!/1
#    prod_{i=0}^{k-1}(3+2i)=3*5*...*(2k+1)=(2k+1)!!/1
#  So u_k ~ 2(-2tau)^k / [ (2tau)^{k+1}(k+1)! * tau^k (2k+1)!! ]
#         = 2 (-2)^k tau^k / [ 2^{k+1} tau^{k+1} (k+1)! tau^k (2k+1)!! ]
#         = (-1)^k / [ tau^{k+1} (k+1)! (2k+1)!! ]   * (2*2^k)/(2^{k+1}) = (-1)^k/(tau^{k+1}(k+1)!(2k+1)!!)
# => u_k(tau) ~ (-1)^k / [ tau^{k+1} (k+1)! (2k+1)!! ]   as tau->0.  Diverges like tau^{-(k+1)}.
def dfac2(n):  # (n)!! odd
    r=mp.mpf(1); i=n
    while i>0: r*=i; i-=2
    return r
print("Verify u_k(tau) ~ (-1)^k / [tau^{k+1} (k+1)! (2k+1)!!]  as tau->0:")
print(" k     u_k(1e-5)            predicted             ratio")
for k in range(0,9):
    t=mp.mpf('1e-5')
    pred = mp.mpf(-1)**k / (t**(k+1) * mp.factorial(k+1) * dfac2(2*k+1))
    act = u_k(k,t)
    print(f"  {k}   {mp.nstr(act,7):>16}  {mp.nstr(pred,7):>16}   {mp.nstr(act/pred,8)}")
print("\n=> For each fixed k, |u_k(tau)| -> infinity like tau^{-(k+1)} as tau->0+.")
print("   So sup_{tau in (0,eps)} |u_k(tau)| = +infinity for every k.  No tau-uniform envelope exists, even at j=0.")
