import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# Sigma = sum_c q^c L_c (1-q^c). Note q^c(1-q^c) and S_c-S_{c+1}=(1-q)q^c L_c.
# So q^c L_c = (S_c - S_{c+1})/(1-q). Then
#   Sigma = sum_c (S_c-S_{c+1})/(1-q) * (1-q^c)  = 1/(1-q) sum_c (S_c-S_{c+1})(1-q^c).
# Abel/summation by parts: sum_c (S_c-S_{c+1}) a_c with a_c=(1-q^c).
#   = sum_c S_c a_c - sum_c S_{c+1}a_c = sum_{c>=1}S_c a_c - sum_{c>=2}S_c a_{c-1}
#   = S_1 a_1 + sum_{c>=2} S_c(a_c-a_{c-1}).   a_c-a_{c-1}=(1-q^c)-(1-q^{c-1})=q^{c-1}-q^c=q^{c-1}(1-q).
#   a_1=1-q.
# => sum_c (S_c-S_{c+1})(1-q^c) = S_1(1-q) + (1-q)sum_{c>=2} S_c q^{c-1}.
# => Sigma = S_1 + sum_{c>=2} S_c q^{c-1}.
# Verify:
for m in [2,4,8,16]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    S=[mp.mpf(0)]*(N+2); acc=mp.mpf(0)
    for a in range(N-1,0,-1):
        acc+=q**a*L[a]; S[a]=(1-q)*acc
    Sig=sum(q**c*L[c]*(1-q**c) for c in range(1,N))
    Sig2=S[1]+sum(S[c]*q**(c-1) for c in range(2,N))
    # Even cleaner: Sigma = sum_{c>=1} S_c q^{c-1}  (since S_1*1 = S_1 q^0)
    Sig3=sum(S[c]*q**(c-1) for c in range(1,N))
    print(f'm={m}: Sig={float(Sig):.6f} Sig2={float(Sig2):.6f} Sig3={float(Sig3):.6f}')
