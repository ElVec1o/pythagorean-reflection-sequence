import mpmath as mp
mp.mp.dps=40

# b0 = 2q/(1-q) + 2q * Sigma,  Sigma=sum_{c>=1} q^c L_c (1-q^c).
# Continuum: Sigma ~ (1/tau) int_0^1 L(u)(1-u) du, L(u)=b0 sin(w(1-u))/sin(w).
# Let s=1-u in [0,1]. int_0^1 sin(w s)/sin(w) * s ds  ... wait (1-u)=s, du=-ds.
# int_0^1 L(u)(1-u)du = b0/sin(w) int_0^1 sin(w(1-u))(1-u) du = b0/sin(w) int_0^1 sin(w s) s ds.
# int_0^1 s sin(ws) ds = [sin(ws)/w^2 - s cos(ws)/w]_0^1 = sin(w)/w^2 - cos(w)/w.
# So Sigma ~ (1/tau)(b0/sin w)(sin w/w^2 - cos w/w) = (b0/tau)(1/w^2 - cos w/(w sin w)).
# Then b0 = 2q/(1-q) + 2q (b0/tau)(1/w^2 - cot(w)/w).
# Recall w^2=2/tau => 1/w^2=tau/2. So 2q(b0/tau)(tau/2)=q b0. And the cot term:
#   2q(b0/tau)(-cot w / w).
# => b0 = 2q/(1-q) + q b0 - 2q b0 cot(w)/(tau w).
# => b0(1-q) = 2q/(1-q) - 2q b0 cot(w)/(tau w)
# => b0[(1-q) + 2q cot(w)/(tau w)] = 2q/(1-q)
# => b0 = 2q/(1-q) / [ (1-q) + 2q cot(w)/(tau w) ].
# At travel poles cot(w)=cos/sin ~ O(sqrt tau)/(±1) -> 0. So denom -> (1-q)~tau.
# => b0 ~ 2q/(1-q)/(1-q) = 2q/(1-q)^2. Hmm that's not 2/tau. (1-q)~tau so 2/tau^2?? wrong.
# Let me just EVALUATE this formula and compare to raw, generic q first.
def raw_local(q,N):
    import importlib
    return None
exec(open('struct_probe.py').read().split('# The forward')[0])

print("GENERIC q test of b0 formula:")
for qf in ['0.9','0.95','0.97','0.99','0.995']:
    q=mp.mpf(qf); N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N)
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    denom=(1-q)+2*q*mp.cot(w)/(tau*w)
    b0f=2*q/(1-q)/denom
    print(f'q={qf} b0={float(b0):.5f} b0formula={float(b0f):.5f} ratio={float(b0f/b0):.4f}')
