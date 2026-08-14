import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# b0 = 2q/(1-q) + 2q*Sigma, Sigma=sum_{c>=1} q^c L_c (1-q^c) -> 1/2 along poles.
# => b0 ~ 2q/(1-q)+q. b0*tau = tau[2q/(1-q)+2q*Sigma].
print(f"{'m':>3}{'Sigma':>11}{'b0':>12}{'2q/(1-q)+q':>13}{'b0*tau':>10}")
for m in [1,2,4,8,16,32,64,79]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    tau=-mp.log(q)
    Sig=sum(q**c*L[c]*(1-q**c) for c in range(1,N))
    approx=2*q/(1-q)+q
    print(f"{m:>3}{float(Sig):>11.6f}{float(b0):>12.5f}{float(approx):>13.5f}{float(b0*tau):>10.6f}")
print()
print("So b0*tau = tau*2q/(1-q) + 2q*tau*Sigma. tau*2q/(1-q) -> 2 (since (1-q)/tau->1, q->1).")
print("2q*tau*Sigma -> 0 since Sigma bounded, tau->0. Hence b0*tau->2.  KEY: Sigma->1/2 (bounded).")
