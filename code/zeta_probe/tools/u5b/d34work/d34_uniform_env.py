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

# The D3.4 route wants:  sup_{tau in (0,eps)} |d^j u_k / dtau^j| =: E_j(k),  with sum_k E_j(k) < infinity.
# CRITICAL TEST: for FIXED k, what is sup_{tau} |u_k(tau)| over (0, eps)? And does sum_k of that converge?
# If even j=0 envelope E_0(k)=sup_tau|u_k| is NOT summable, the route is dead at j=0.
#
# u_k(tau) for small tau:  q->1, (1-q)~tau, so (-2(1-q))^k ~ (-2tau)^k -> 0, BUT denominator (q^2;q^2)_{k+1} ~ prod (1-q^{2i})
#   ~ prod (2i*tau) ~ (2tau)^{k+1}(k+1)! ... let's just compute sup over a tau-grid in (0,eps).
eps = mp.mpf('0.05')
print("E_0(k) = sup_{tau in (0,0.05)} |u_k(tau)|, and is sum_k E_0(k) finite?")
print(" k    argmax tau     E_0(k)=sup|u_k|     u_k(eps)        u_k(tau->0 limit?)")
cumsum=mp.mpf(0)
for k in range(0,26):
    # scan tau
    mx=mp.mpf(0); targ=None
    NT=240
    for i in range(1,NT+1):
        t=eps*mp.mpf(i)/NT
        v=abs(u_k(k,t))
        if v>mx: mx=v; targ=t
    cumsum+=mx
    # small-tau limit of u_k: compute at tiny tau
    small=u_k(k, mp.mpf('1e-6'))
    print(f"  {k:3d}  {mp.nstr(targ,4):>10}   {mp.nstr(mx,8):>14}   {mp.nstr(u_k(k,eps),5):>12}   {mp.nstr(small,5):>12}   cumsum={mp.nstr(cumsum,6)}")
print(f"\n  partial sum_k E_0(k) (k<=25) = {mp.nstr(cumsum,8)}  -- growing? check trend of E_0(k)")
