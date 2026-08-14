import mpmath as mp
mp.mp.dps=40
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

def v_at(q,bstop):
    q=mp.mpf(q); N=int(60/(1-q)); v=mp.mpf(0)
    for b in range(N,bstop,-1):
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        v=(v*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*v)
    return v  # this is v_bstop

# v_1 at generic q vs travel poles. Is v_1=-2/3 a defining pole condition?
print("Generic q:")
for qf in ['0.99','0.995','0.999']:
    q=mp.mpf(qf); v1=v_at(q,1); tau=-mp.log(q); w=mp.sqrt(2/tau)
    print(f'  q={qf} w={float(w):.4f} cos w={float(mp.cos(w)):+.4f} v1={float(v1):.6f}')
print("Travel poles (cos w ~0, sin w=+-1):")
for m in [4,8,16,32]:
    q=poles[m-1]; v1=v_at(q,1); tau=-mp.log(q); w=mp.sqrt(2/tau)
    print(f'  m={m} w={float(w):.4f} cos w={float(mp.cos(w)):+.5f} v1={float(v1):.6f}')
