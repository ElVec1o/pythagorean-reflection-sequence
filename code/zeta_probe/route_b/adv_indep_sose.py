import mpmath as mp
mp.mp.dps=60

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
    return dict(b0=l0,b1=l1,t0=u0[0],t1=u1[0],v0=v[0])

def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p
def Se_So(q):
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    for j in range(0,4000):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te; So+=to
        if j>10 and abs(te)+abs(to)<mp.mpf(10)**(-80): break
    return Se,So

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("So/Se->1 ONLY at poles; closed-form b0=(2q/p)So/Se holds everywhere. P12=t1*Se trivial.")
print(f"{'tag':>8} {'So/Se':>14} {'|b0-(2q/p)So/Se|':>18} {'P12=t1*Se':>12}")
for tag,q in [('q=.6',mp.mpf('0.6')),('q=.8',mp.mpf('0.8'))]+[('p%d'%m,poles[m-1]) for m in [1,2,4,8,12]]:
    N=int(60/(1-q)); r=raw(q,N); Se,So=Se_So(q); p=1-q
    chk=abs(r['b0']-(2*q/p)*So/Se); P12=r['t1']*Se
    print(f"{tag:>8} {float(So/Se):>14.9f} {mp.nstr(chk,2):>18} {float(P12):>12.7f}")
print("EXIT")
