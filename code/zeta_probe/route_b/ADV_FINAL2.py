import mpmath as mp
mp.mp.dps=50

def raw(q,N):
    q=mp.mpf(q); qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1); u0=[mp.mpf(0)]*(N+1); u1=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=mp.mpf(0); l1=mp.mpf(0); L=[mp.mpf(0)]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd
        L.append(l0)
    return dict(b0=l0,b1=l1,t0=u0[0],t1=u1[0],v0=v[0],L=L,qp=qp)

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*100)
print("CHECK 1: b0*tau<->SUM->1/2 ; t1==v0 ; b1==t0  (raw-only, stable to m=48)")
print("="*100)
print(f"{'m':>3} {'tau':>10} {'b0*tau':>14} {'SUM':>16} {'|t1-v0|':>10} {'|b1-t0|':>10}")
for m in [1,2,4,8,16,24,32,40,48]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); N=int(55/(1-q)); r=raw(q,N)
    SUM=q*sum(r['qp'][b]*r['L'][b]*(1-r['qp'][b]) for b in range(1,N))
    print(f"{m:>3} {float(tau):>10.6f} {float(r['b0']*tau):>14.10f} {float(SUM):>16.12f} {float(abs(r['t1']-r['v0'])):>10.2e} {float(abs(r['b1']-r['t0'])):>10.2e}")

print()
print("="*100)
print("CHECK 2: SIGN MARGIN (actual B_U!=0 input): b0>0 AND s<1 at EVERY pole m=1..48")
print("="*100)
viol=0; maxs=mp.mpf(0); minb0=mp.mpf('1e9')
for m in range(1,49):
    if m>len(poles): break
    q=poles[m-1]; N=int(55/(1-q)); r=raw(q,N); s=(q/(1-q))*r['t1']
    if s>=1 or r['b0']<=0: viol+=1
    if s>maxs: maxs=s
    if r['b0']<minb0: minb0=r['b0']
print(f"  violations (s>=1 or b0<=0): {viol}/48   max s = {float(maxs):.8f}   min b0 = {float(minb0):.4f}")
print("  => B_U = (1-s)B_V + q*b0 ; B_V>0, (1-s)>0, b0>0 => B_U>0 != 0")

print()
print("="*100)
print("CHECK 3: probe a clean exact relation behind reciprocity. b0*t1 -> 1/2 ?")
print("="*100)
print(f"{'m':>3} {'b0*t1':>12} {'(b0*t1-1/2)/tau':>16}  {'generic q b0*t1':>16}")
for m in [1,2,4,8,16,24,32]:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); N=int(55/(1-q)); r=raw(q,N)
    print(f"{m:>3} {float(r['b0']*r['t1']):>12.8f} {float((r['b0']*r['t1']-mp.mpf(1)/2)/tau):>16.8f}")
print(" generic q b0*t1 (should NOT be 1/2 if pole-only):")
for tt in ['0.6','0.8','0.9']:
    q=mp.mpf(tt); N=int(55/(1-q)); r=raw(q,N)
    print(f"   q={tt}: b0*t1={float(r['b0']*r['t1']):.6f}")
print("EXIT=0")
