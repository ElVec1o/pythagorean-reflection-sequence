import mpmath as mp
mp.mp.dps=30

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
    l0=mp.mpf(0); l1=mp.mpf(0); L=[mp.mpf(0)]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd; L.append(l0)
    return l0,l1,u0[0],u1[0],L,v
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

print("="*78)
print("CONSOLIDATED DERIVATION CHECK (formulas vs raw() and poles.txt)")
print("="*78)
print("\n--- IDENTITY A (exact): b0 = 2q/(1-q) + 2q*Sigma, Sigma=sum_{c>=1} S_c q^{c-1} ---")
print("    S_c=(1-q) sum_{a>=c} q^a L_a  (bounded current). Claim Sigma->1/2.")
print(f"{'m':>3}{'b0(raw)':>13}{'b0=2q/(1-q)+2qSig':>20}{'Sigma':>10}{'b0*tau':>10}")
for m in [1,2,4,8,16,32,64,79]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q)
    b0,b1,t0,t1,L,v=raw(q,N)
    # current S_c via O(N) backward cumsum
    acc=mp.mpf(0); S=[mp.mpf(0)]*(N+1)
    for a in range(N-1,0,-1):
        acc+=q**a*L[a]; S[a]=(1-q)*acc
    Sig=sum(S[c]*q**(c-1) for c in range(1,N))
    b0_id=2*q/(1-q)+2*q*Sig
    print(f"{m:>3}{float(b0):>13.5f}{float(b0_id):>20.5f}{float(Sig):>10.6f}{float(b0*tau):>10.6f}")

print("\n--- LIMIT (I): b0*tau = [2q*tau/(1-q)] + [2q*tau*Sigma] -> 2*1 + 0 = 2 ---")
print("    2q*tau/(1-q): tau/(1-q)->1 (since 1-q=tau-tau^2/2+..), q->1  => ->2")
print("    2q*tau*Sigma: Sigma bounded, tau->0  => ->0")

print("\n--- IDENTITY B (exact chain): t1 = u1[0] = v[0] (v-Riccati boundary value) ---")
print(f"{'m':>3}{'t1(raw)':>14}{'v[0]':>14}{'s=gV*t1':>10}")
for m in [1,2,4,8,16,32,64,79]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L,v=raw(q,N)
    gV=q/(1-q)
    print(f"{m:>3}{float(t1):>14.8f}{float(v[0]):>14.8f}{float(gV*t1):>10.6f}")

print("\n--- LIMIT (II) mechanism: v0=(v1(1+2q^2)+2q^3)/(1-2q^2-2q v1), v1->-2/3 (pole sig) ---")
print("    Taylor: v1=-2/3+(41/36)tau  =>  v0 -> tau/4  =>  s=q/(1-q)*v0 -> 1/4")
print(f"{'m':>3}{'v1':>12}{'(v1+2/3)/tau':>14}{'v0/tau':>10}{'s':>10}")
for m in [4,8,16,32,64]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q)
    b0,b1,t0,t1,L,v=raw(q,N)
    v0=v[0]; v1=v[1]; gV=q/(1-q)
    print(f"{m:>3}{float(v1):>12.7f}{float((v1+mp.mpf(2)/3)/tau):>14.6f}{float(v0/tau):>10.6f}{float(gV*t1):>10.6f}")
print("\n  41/36 =",float(mp.mpf(41)/36),"   target v0/tau=1/4=0.25, s=1/4")
