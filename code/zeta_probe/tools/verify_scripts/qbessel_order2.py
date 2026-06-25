import mpmath as mp
mp.mp.dps = 50
# robust version using mpmath's q-Pochhammer mp.qp for the infinite products
def J3(nu,x,q,N=300):
    pref = mp.qp(q**(nu+1),q)/mp.qp(q,q)        # (q^{nu+1};q)_inf/(q;q)_inf
    def term(n):
        return (-1)**n*q**(mp.mpf(n*(n-1))/2)*(q*x*x)**n/(mp.qp(q**(nu+1),q,n)*mp.qp(q,q,n))
    return pref*x**nu*mp.fsum(term(n) for n in range(N))
nu=mp.mpf(3)/2; A=mp.mpf(4)
cls=mp.besselj(nu,A)
print(f"q-Bessel J^(3)_3/2 -> classical J_3/2({float(A)})={mp.nstr(cls,12)} ; relative gap (ratio-1)/tau should -> const:")
rows=[]
for taus in ['0.04','0.02','0.01','0.005','0.0025','0.00125']:
    tau=mp.mpf(taus); q=mp.e**(-tau); x=A*(1-q)/2
    r=J3(nu,x,q)/cls
    rows.append((tau,r))
    print(f"  tau={taus:>8}:  ratio-1 = {mp.nstr(r-1,10):>16}   (ratio-1)/tau = {mp.nstr((r-1)/tau,8)}")
print("  => (ratio-1)/tau settling to a constant = clean O(tau) relative = R=O(tau^{5/2}).  Richardson:")
# Richardson extrapolate (ratio-1)/tau to tau=0
seq=[(r-1)/tau for tau,r in rows]
a=[mp.mpf(v.real) for v in seq]
for _ in range(len(a)-1):
    a=[(2*a[i+1]-a[i]) for i in range(len(a)-1)]   # halving Richardson
print(f"     Richardson limit of (ratio-1)/tau  -> {mp.nstr(a[0],8)}   (the universal O(tau) amplitude coeff)")
