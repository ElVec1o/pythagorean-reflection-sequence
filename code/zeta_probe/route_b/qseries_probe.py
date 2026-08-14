import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

# Claim: L_b = sum_{k>=0} c_k q^{kb}, with
#   c_k = 2(1-q) q c_{k-2} / [ (1-q^k)(1-q^{1-k}) ]
# Plug L_b=q^{kb} into homogeneous recursion to see which k are roots & the inhomog coupling.
# Recursion: L_{b+1} - (1+q) L_b + q L_{b-1} = 2(1-q) q^{2b+1} L_b
# LHS with L_b=q^{kb}: q^{k(b+1)} - (1+q)q^{kb} + q q^{k(b-1)} = q^{kb}(q^k - (1+q) + q^{1-k})
#   = q^{kb} (q^k -1)(1 - q^{1-k})  [check: (q^k-1)(1-q^{1-k}) = q^k -q^{2k-... let's just verify]
# RHS with L_b sum: 2(1-q) q^{2b+1} sum_j c_j q^{jb} = sum_j 2(1-q) q c_j q^{(j+2)b}
# Matching q^{kb}: c_k (q^k-1)(1-q^{1-k}) = 2(1-q) q c_{k-2}
# => c_k = 2(1-q) q c_{k-2} / [ (q^k-1)(1-q^{1-k}) ]
# Note (q^k-1)(1-q^{1-k}) = -(1-q^k)(1-q^{1-k}). Sign matters. Let me just verify numerically.

def factor(q,k):
    return (q**k-1)*(1-q**(1-k))

for q in [mp.mpf('0.9'), mp.mpf('0.95')]:
    N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N)
    L=[mp.mpf(0)]+L0
    # Fit c_0, c_1 then propagate even & odd chains; reconstruct L_b at moderate b, compare.
    # c_0 = b0 (limit). c_1 free from L_0=0: L_0 = sum_k c_k = 0.
    c0=b0
    # even chain: c_0 -> c_2 -> c_4..., odd chain: c_1 -> c_3 ->...
    # c_1 determined by L_0=0: sum_{k>=0} c_k =0.
    # Build even chain
    Kmax=400
    ceven={0:c0}
    for k in range(2,Kmax,2):
        ceven[k]=2*(1-q)*q*ceven[k-2]/factor(q,k)
    # odd chain in terms of c1: c_k = alpha_k * c1
    alpha={1:mp.mpf(1)}
    for k in range(3,Kmax,2):
        alpha[k]=2*(1-q)*q*alpha[k-2]/factor(q,k)
    seven=sum(ceven.values())
    salpha=sum(alpha.values())
    c1=-seven/salpha
    print(f'q={float(q)} c0=b0={float(c0):.6f} c1={float(c1):.6f}  (naive -2q/(1-q)={float(-2*q/(1-q)):.4f})')
    # Reconstruct L_b
    def Lrec(b):
        s=ceven[0]
        for k in range(2,Kmax,2): s+=ceven[k]*q**(k*b)
        for k in range(1,Kmax,2): s+=alpha[k]*c1*q**(k*b)
        return s
    err=max(abs(Lrec(b)-L[b]) for b in range(0,min(N,30)))
    print(f'   max recon err over b=0..30: {float(err):.3e}')
