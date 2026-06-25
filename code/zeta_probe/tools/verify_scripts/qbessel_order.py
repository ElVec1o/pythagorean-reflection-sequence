import mpmath as mp
mp.mp.dps = 40
# Morita's Hahn-Exton q-Bessel:
#  J^(3)_nu(x;q) = [(q^{nu+1};q)_inf/(q;q)_inf] x^nu sum_n (-1)^n q^{n(n-1)/2} (q x^2)^n /((q^{nu+1};q)_n (q;q)_n)
# Classical limit (q->1): -> J_nu(2x/(1-q)) up to a constant.  Hold the effective argument A=2x/(1-q) FIXED
# and check the relative convergence rate in tau (q=e^{-tau}).  O(tau) relative <=> R=O(tau^{5/2}).
def qpoch(a,q,n):
    r=mp.mpf(1)
    for k in range(n): r*=(1-a*q**k)
    return r
def qpoch_inf(a,q,N=2000):
    r=mp.mpf(1)
    for k in range(N):
        t=1-a*q**k; r*=t
        if abs(t-1)<mp.mpf(10)**(-50): break
    return r
def J3(nu,x,q,N=200):
    pref=qpoch_inf(q**(nu+1),q)/qpoch_inf(q,q)
    s=mp.fsum((-1)**n*q**(mp.mpf(n*(n-1))/2)*(q*x*x)**n/(qpoch(q**(nu+1),q,n)*qpoch(q,q,n)) for n in range(N))
    return pref*x**nu*s
nu=mp.mpf(3)/2
for A in [mp.mpf(4), mp.mpf(7)]:           # fixed effective Bessel argument (oscillatory regime)
    print(f"=== effective argument A=2x/(1-q) = {float(A)} ;  classical J_3/2(A)={mp.nstr(mp.besselj(nu,A),10)} ===")
    rows=[]
    for taus in ['0.02','0.01','0.005','0.0025']:
        tau=mp.mpf(taus); q=mp.e**(-tau); x=A*(1-q)/2
        val=J3(nu,x,q)
        cls=mp.besselj(nu,A)
        rows.append((tau, val/cls))     # ratio q-Bessel / classical (-> const as tau->0)
        print(f"  tau={taus}:  J3/J_classical = {mp.nstr(val/cls,14)}")
    # the ratio -> L; check (ratio-L) ~ tau (linear) by successive-difference ratios -> 2
    print("  successive-diff ratios of (J3/J_cls) (->2.0 means O(tau) relative, no sqrt):")
    for i in range(len(rows)-2):
        d1=rows[i][1]-rows[i+1][1]; d2=rows[i+1][1]-rows[i+2][1]
        print(f"     {mp.nstr(d1/d2,8)}")
