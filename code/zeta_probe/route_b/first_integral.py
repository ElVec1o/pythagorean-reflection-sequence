import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

# Look for a first integral / summed form. Original 1st-order system (source0):
#   L_b = L_{b-1} + 2q^b + 2 q^b S_b      ... (i)
#   S_{b+1} = S_b - (1-q) q^b L_b         ... (ii)
# As b->inf: L->b0, S->0 (resolvent converges; check). Sum (ii) from b to inf:
#   S_inf - S_b = -(1-q) sum_{a>=b} q^a L_a  => S_b = (1-q) sum_{a>=b} q^a L_a  (S_inf=0)
# Sum (i): L_b - L_0 = sum_{a=1}^b [2q^a + 2q^a S_a]; b0-0 = 2 sum_{a>=1} q^a(1+S_a).
# So b0 = 2 sum_{a>=1} q^a (1+S_a).  Let's verify, and S_b=(1-q)sum_{a>=b}q^a L_a.
for qf in ['0.9','0.99']:
    q=mp.mpf(qf); N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    # reconstruct S_b
    S=[mp.mpf(0)]*(N+2)
    for b in range(N,0,-1):
        S[b]=(1-q)*sum(q**a*L[a] for a in range(b,N))  # tail
    b0rec=2*sum(q**a*(1+S[a]) for a in range(1,N))
    print(f'q={qf} b0={float(b0):.6f} b0rec={float(b0rec):.6f} S_1={float(S[1]):.6f}')
    # check (i): L_b-L_{b-1} =? 2q^b(1+S_b)
    res=max(abs(L[b]-L[b-1]-2*q**b*(1+S[b])) for b in range(1,30))
    print('   recurrence (i) residual:',float(res))
