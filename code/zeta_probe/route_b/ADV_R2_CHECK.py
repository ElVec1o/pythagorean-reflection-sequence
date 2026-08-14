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

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*100)
print("PART C: R2 reciprocity  t1*(2 b0) -> 1  AT TRAVEL POLES  vs GENERIC q")
print("="*100)
print("At travel poles:")
print(f"{'m':>3} {'tau':>10} {'t1':>14} {'b0':>14} {'t1*2*b0':>14} {'(t1*2b0-1)/tau':>16} {'s=gV*t1':>12} {'t1/tau':>11}")
for m in [1,2,4,8,16,24,32]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); gV=q/(1-q); N=int(55/(1-q)); r=raw(q,N)
    t1=r['t1']; b0=r['b0']; s=gV*t1
    print(f"{m:>3} {float(tau):>10.6f} {float(t1):>14.9f} {float(b0):>14.8f} {float(t1*2*b0):>14.9f} {float((t1*2*b0-1)/tau):>16.8f} {float(s):>12.8f} {float(t1/tau):>11.7f}")

print()
print("At GENERIC q (NOT poles) -- is t1*2b0->1 generic or pole-only?")
print(f"{'q':>8} {'t1':>14} {'b0':>14} {'t1*2*b0':>14}  {'t1*b0':>12}")
for tt in ['0.5','0.6','0.7','0.8','0.9','0.95','0.99']:
    q=mp.mpf(tt); N=int(90/(1-q)); r=raw(q,N)
    print(f"{tt:>8} {float(r['t1']):>14.8f} {float(r['b0']):>14.8f} {float(r['t1']*2*r['b0']):>14.8f}  {float(r['t1']*r['b0']):>12.6f}")

print()
print("="*100)
print("PART D: CIRCULARITY AUDIT for R2.")
print(" Colleague: R2 = R1 (b0~2/tau) + t1*2b0->1  =>  t1~1/(2b0)~tau/4.")
print(" Test t1/tau->1/4 DIRECTLY (NOT via b0), to see if R2 stands without invoking R1:")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'t1/tau':>14} {'|t1/tau-1/4|':>14} {'(t1/tau-1/4)/tau':>17}")
for m in [1,2,4,8,16,24,32]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); N=int(55/(1-q)); r=raw(q,N)
    val=r['t1']/tau
    print(f"{m:>3} {float(tau):>10.6f} {float(val):>14.9f} {float(abs(val-mp.mpf(1)/4)):>14.3e} {float((val-mp.mpf(1)/4)/tau):>17.9f}")
print(" -> 1/16 =", float(mp.mpf(1)/16))
