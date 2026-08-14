import mpmath as mp
mp.mp.dps = 40

def raw(q,N):
    q = mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
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
    return l0,l1,u0[0],u1[0]

def Nfor(q): return int(50/(1-q))

# Check the two limits at travel poles
poles=[]
with open('poles.txt') as f:
    for line in f:
        parts=line.split()
        if not parts: continue
        poles.append(mp.mpf(parts[-1]))

print("=== Limits along travel poles ===")
print(f"{'m':>3} {'q':>12} {'b0*tau':>12} {'s=gV*t1':>12}")
for m in [1,2,4,8,16,32,64,79]:
    q=poles[m-1]
    N=Nfor(q)
    b0,b1,t0,t1=raw(q,N)
    tau=-mp.log(q)
    w=mp.sqrt(2/tau)
    gV=q/(1-q)
    s=gV*t1
    print(f"{m:>3} {float(q):>12.8f} {float(b0*tau):>12.7f} {float(s):>12.7f}")
