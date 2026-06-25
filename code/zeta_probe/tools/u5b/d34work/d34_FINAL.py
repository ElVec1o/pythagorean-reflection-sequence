import mpmath as mp
mp.mp.dps = 40
def qpoch(a, base, n):
    pr = mp.mpf(1); ai = mp.mpf(1)*a
    for i in range(n):
        pr *= (1 - ai); ai *= base
    return pr
def u_k(k, tau):
    q = mp.e**(-tau); p = q*q
    return 2*q*(-2*(1-q))**k*q**(k*k+2*k)/(qpoch(p,p,k+1)*qpoch(q*p,p,k))
def Sigma(tau):
    K=int(60/mp.sqrt(tau))+50
    return mp.fsum([u_k(k,tau) for k in range(K+1)])

print("="*70)
print("ROUTE D3.4 FINAL VERDICT — three independent obstructions")
print("="*70)

print("\n[1] The GOAL OBJECT is not even C^0 at 0:")
print("    Sigma(tau) oscillates across [0,2] as tau->0 (tracks 1-cos(sqrt(2/tau))).")
# show two nearby tau with very different Sigma
t1=mp.mpf('0.008'); t2=mp.mpf('0.0056')
print(f"    Sigma({t1})={mp.nstr(Sigma(t1),5)}  vs  Sigma({t2})={mp.nstr(Sigma(t2),5)}  (1.995 vs 0.0006)")
print("    => 'Sigma is C^infty on [0,eps)' is literally FALSE; lim_{tau->0}Sigma DNE.")

print("\n[2] D3.4's per-term envelope is +infinity ALREADY at j=0:")
print("    u_k(tau) ~ (-1)^k / [tau^{k+1}(k+1)!(2k+1)!!]  ->  infinity as tau->0, each fixed k.")
print(f"    e.g. u_3(1e-4)={mp.nstr(u_k(3,mp.mpf('1e-4')),5)}, u_3(1e-5)={mp.nstr(u_k(3,mp.mpf('1e-5')),5)} (grows tau^-4)")
print("    => sup_{tau in(0,eps)}|u_k|=+inf for every k; NO tau-uniform summable envelope exists.")

print("\n[3] The summed derivatives blow up as tau->0 (consistent with [1]):")
for j in range(0,4):
    t=mp.mpf('0.01'); K=int(50/mp.sqrt(t))+40
    S=mp.fsum([mp.diff(lambda x:u_k(k,x),t,j) for k in range(K+1)])
    print(f"    d^{j}Sigma/dtau^{j} at tau=0.01 = {mp.nstr(S,6)}")
print("    These do NOT converge as tau->0 (they oscillate w/ amplitude ~tau^{-3j/2}).")

print("\n[4] At FIXED tau>0 the k-sum DOES converge (Gaussian e^{-k^2 tau} wins):")
print("    so Sigma is real-ANALYTIC on (0,eps); the failure is purely the tau->0 boundary.")
