import mpmath as mp
mp.mp.dps=90

def raw(q,N):
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

# INDEPENDENT cocycle P12, Se (does NOT use t1) -- linear recursion from x0,X0
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y   # P12, P22=Se

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("CHECK 1: t1 = P12/Se EXACT, where P12 from INDEPENDENT cocycle (no t1 inside). NOT circular.")
print(f"{'m':>3} {'tau':>10} {'t1_raw':>16} {'P12/Se':>16} {'rel.diff':>10}")
for m in [1,2,4,8,16,32,50,70]:
    q=poles[m-1]; tau=-mp.log(q); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N)
    rel=abs(t1-P12/Se)/abs(t1)
    print(f"{m:>3} {float(tau):>10.3e} {float(t1):>16.10e} {float(P12/Se):>16.10e} {float(rel):>10.2e}")

print()
print("CHECK 2: the THREE asymptotic claims independently. P12pred=sinw*tau^1.5/(4sqrt2), Sepred=sqrt(tau/2)sinw.")
print("  Each ratio must ->1 on its OWN. If P12ratio->1 INDEPENDENTLY, the saddle est is not assuming t1.")
print(f"{'m':>3} {'tau':>10} {'P12ratio':>12} {'(P12r-1)/tau':>13} {'Seratio':>12} {'(Ser-1)/tau':>12} {'t1/(tau/4)':>11}")
for m in [2,4,8,16,24,32,40,50,60,70,78]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N); P12,Se=cocycle(q,N)
    sw=mp.sin(w)
    p12pred=sw*tau**mp.mpf('1.5')/(4*mp.sqrt(2)); sepred=mp.sqrt(tau/2)*sw
    rp=P12/p12pred; rs=Se/sepred
    print(f"{m:>3} {float(tau):>10.3e} {float(rp):>12.8f} {float((rp-1)/tau):>13.6f} {float(rs):>12.8f} {float((rs-1)/tau):>12.6f} {float(t1/(tau/4)):>11.8f}")

print()
print("CHECK 3: DECIDING-SUBLEADING audit. The chain uses Se~sqrt(tau/2)sinw (LEADING). But Se has")
print("  subleading O(tau)*sinw and the lem:cos T2~sqrt2/36 sqrt(tau) cosw piece. Does dropping them")
print("  change the LIMIT of t1/(tau/4)? Compare t1/(tau/4) vs P12pred/Sepred (both LEADING preds):")
print(f"{'m':>3} {'t1/(tau/4) [true]':>18} {'P12pred/Sepred/(tau/4)':>22} {'these agree?':>12}")
for m in [4,8,16,32,60]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    b0,b1,t0,t1=raw(q,N)
    sw=mp.sin(w)
    p12pred=sw*tau**mp.mpf('1.5')/(4*mp.sqrt(2)); sepred=mp.sqrt(tau/2)*sw
    leadquot=(p12pred/sepred)/(tau/4)
    print(f"{m:>3} {float(t1/(tau/4)):>18.10f} {float(leadquot):>22.10f} {abs(t1/(tau/4)-leadquot)<1e-9}")
print("  Note: P12pred/Sepred = [tau^1.5/(4sqrt2)]/[sqrt(tau/2)] = tau/4 EXACTLY (sinw cancels).")
print("  So leadquot==1 identically; the LIMIT 1 comes from the two leading preds. The deciding")
print("  subleading lives in HOW FAST each ratio ->1, not the limit. Limit is safe IF both preds proven.")

print()
print("CHECK 4: is P12's saddle prediction CIRCULAR? Compute P12 saddle amplitude w/o ANY t1 reference,")
print("  i.e. |P12|/tau^1.5 -> 1/(4sqrt2)*|sinw|. At poles |sinw|=1.")
print(f"{'m':>3} {'|P12|/tau^1.5':>16} {'1/(4sqrt2)=':>14} {'ratio':>10} {'|sinw|':>10}")
inv=1/(4*mp.sqrt(2))
for m in [2,4,8,16,32,60]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    P12,Se=cocycle(q,N)
    amp=abs(P12)/tau**mp.mpf('1.5')
    print(f"{m:>3} {float(amp):>16.10f} {float(inv):>14.10f} {float(amp/inv):>10.7f} {float(abs(mp.sin(w))):>10.7f}")
