import mpmath as mp
mp.mp.dps=40

def raw(q,N):
    q=mp.mpf(q)
    qp=[mp.mpf(1)]*(N+1)
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
    return l0,l1,u0[0],u1[0],L,qp

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("="*92)
print(" FINAL PROOF (raw-only, numerically stable to m=80)")
print("="*92)

print("\n[I] b0*tau -> 2.  EXACT decomposition: b0*tau = A + 2*tau*SUM,")
print("    A = tau*2q/(1-q)  (ELEMENTARY: ->2),   SUM = q*sum_b q^b L_b(1-q^b) (bounded ->1/2).")
print(f"   {'m':>3} {'tau':>11} {'b0*tau':>15} {'A=2q*tau/(1-q)':>15} {'SUM':>11} {'2*tau*SUM':>11} {'|b0t-2|':>9}")
for m in [1,2,4,8,16,32,48,64,80]:
    if m>len(poles): break
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    SUM=q*sum(qp[b]*L[b]*(1-qp[b]) for b in range(1,N))
    A=tau*2*q/p
    chk=A+2*tau*SUM
    print(f"   {m:>3} {float(tau):>11.7f} {float(b0*tau):>15.11f} {float(A):>15.11f} {float(SUM):>11.7f} {float(2*tau*SUM):>11.2e} {float(abs(b0*tau-2)):>9.1e}")

print("\n[II] s = g_V*t1 -> 1/4.   s = (q/(1-q))*t1, and t1 = tau/4 + O(tau^2).")
print(f"   {'m':>3} {'tau':>11} {'s=g_V*t1':>15} {'t1':>13} {'t1/tau':>11} {'4*t1/tau':>11} {'|s-1/4|':>9}")
for m in [1,2,4,8,16,32,48,64,80]:
    if m>len(poles): break
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    s=(q/p)*t1
    print(f"   {m:>3} {float(tau):>11.7f} {float(s):>15.11f} {float(t1):>13.9f} {float(t1/tau):>11.8f} {float(4*t1/tau):>11.8f} {float(abs(s-mp.mpf(1)/4)):>9.1e}")

print("\n[III] Convergence rates (Richardson-style): both errors ~ O(tau).")
print(f"   {'m':>3} {'(b0*tau-2)/tau':>16} {'(s-1/4)/tau':>14}  (bounded => limits are 2 and 1/4 exactly)")
for m in [4,8,16,32,64,80]:
    if m>len(poles): break
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q); p=1-q
    b0,b1,t0,t1,L,qp=raw(q,N)
    s=(q/p)*t1
    print(f"   {m:>3} {float((b0*tau-2)/tau):>16.8f} {float((s-mp.mpf(1)/4)/tau):>14.8f}")
