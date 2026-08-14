import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# Efficient: S via backward cumulative (O(N)).
for m in [2,4,8]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    # backward cumsum for S_b=(1-q)sum_{a>=b} q^a L_a
    S=[mp.mpf(0)]*(N+1)
    acc=mp.mpf(0)
    for a in range(N-1,0,-1):
        acc+=q**a*L[a]; S[a]=(1-q)*acc
    Sig=mp.mpf(0)
    for c in range(1,N):
        Sig+=q**c*L[c]*(1-q**c)
    sumqL=acc  # sum_{a>=1} q^a L_a
    T=mp.mpf(0)
    for c in range(1,N):
        T+=q**(2*c)*L[c]
    print(f'm={m}: Sig={float(Sig):.6f} S1={float(S[1]):.6f} sumqL={float(sumqL):.5f} T={float(T):.5f} Sig=sumqL-T? {float(sumqL-T):.6f}')
