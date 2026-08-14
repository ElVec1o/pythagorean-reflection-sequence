import mpmath as mp
mp.mp.dps=30
# Is v0~tau/4 generic (not pole-specific)? Test at arbitrary q close to 1.
def v0(q):
    q=mp.mpf(q); N=int(80/(1-q))
    v=mp.mpf(0)
    for b in range(N,0,-1):
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        v=(v*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*v)
    return v
for qf in ['0.9','0.95','0.99','0.995','0.999','0.9999']:
    q=mp.mpf(qf); tau=-mp.log(q); v=v0(q)
    print(f'q={qf}: v0={float(v):.8f} v0/tau={float(v/tau):.6f} s=gV v0={float(q/(1-q)*v):.6f}')
