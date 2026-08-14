import mpmath as mp
mp.mp.dps = 40
def raw(q, N):
    qp = [mp.mpf(1)]*(N+1)
    for b in range(1, N+1): qp[b] = qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b];q2b=qb*qb;q3b=q2b*qb;dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd;c0=2*qb;c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]);v[b-1]=vb
    l0=mp.mpf(0);l1=mp.mpf(0)
    for b in range(1,N+1):
        qb=qp[b];q2b=qb*qb;dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd;l1=(l1+2*q2b+2*qb*u1[b])/dd
    return l0,l1,u0[0],u1[0]
def Nfor(q): return int(50/(1-q))+5
print("=== off-pole s blowup (colleague claims s=-26.8,-123,... and ~ -1/tau) ===")
for q in [mp.mpf('0.99'),mp.mpf('0.992'),mp.mpf('0.994')]:
    l0,l1,t0,t1=raw(q,Nfor(q))
    s=q/(1-q)*t1
    print(f" q={float(q)} s={mp.nstr(s,8)}  s*tau={mp.nstr(s*(-mp.log(q)),6)}")
print("=== also b0*tau off these same non-pole q (should NOT be 2) ===")
for q in [mp.mpf('0.99'),mp.mpf('0.992'),mp.mpf('0.994')]:
    l0,l1,t0,t1=raw(q,Nfor(q))
    print(f" q={float(q)} b0*tau={mp.nstr(l0*(-mp.log(q)),8)}")
