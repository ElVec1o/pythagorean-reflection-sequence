import mpmath as mp
mp.mp.dps=30
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# v_b array along a pole. v_{b-1}=(v_b(1+2q2b)+2q3b)/(1-2q2b-2qb v_b).
# Linearize for small v (v~tau): v_{b-1}~v_b(1+2q2b)+2q3b + 2qb v_b*(v_b+...)+ (denom expand)
# To leading order in small q^b region (b large): v_{b-1}~v_b+2q^{3b} -> v accumulates q^{3b}.
# But near turning point q^b~1/w (q2b~1/w^2~tau/2) terms ~q^{2b} matter. This is Riccati of
# the SAME Bessel equation. v_b is essentially the log-derivative of the bulk solution.
# Let's get v_b array and compare v_b/tau to a Bessel-ratio ansatz. First inspect shape.
m=8; q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
varr=[mp.mpf(0)]*(N+1)
for b in range(N,0,-1):
    qb=q**b; q2b=qb*qb; q3b=q2b*qb
    varr[b-1]=(varr[b]*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*varr[b])
print('m',m,'w',float(w),'tau',float(tau))
for b in [0,1,2,4,8,16,32,64,128]:
    if b>N: break
    z=w*q**b
    print(f'  b={b:>4} v_b/tau={float(varr[b]/tau):>10.5f} z=wq^b={float(z):>8.3f} q^b={float(q**b):.4f}')
