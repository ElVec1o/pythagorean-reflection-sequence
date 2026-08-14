import mpmath as mp
mp.mp.dps=40
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# Look at v_b for small b along a high pole: do v_1,v_2,... all -> -2/3? or just v_1?
for m in [32]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    varr=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        varr[b-1]=(varr[b]*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*varr[b])
    print(f'm={m} w={float(w):.3f}')
    for b in [0,1,2,3,5,10,20,40,80]:
        z=w*q**b
        print(f'  b={b:>3} v_b={float(varr[b]):>12.7f} (v_b+2/3)/tau={float((varr[b]+mp.mpf(2)/3)/tau):>10.4f} z={float(z):.3f}')
