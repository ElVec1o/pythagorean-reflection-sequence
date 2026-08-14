import math

def raw_f(q,N):
    qp=[1.0]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[0.0]*(N+1); u0=[0.0]*(N+1); u1=[0.0]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=0.0; l1=0.0; L=[0.0]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; l1=(l1+2*q2b+2*qb*u1[b])/dd; L.append(l0)
    return l0,l1,u0[0],u1[0],L,v

poles=[float(l.split()[-1]) for l in open('poles.txt') if l.split()]

print("="*86)
print("CONSOLIDATED CHECK (float64; >=5 sig figs).  Formula vs raw() and poles.txt")
print("="*86)
print("\nIDENTITY A (exact): b0 = 2q/(1-q) + 2q*Sigma,  Sigma = sum_{c>=1} S_c q^{c-1}")
print(f"{'m':>3}{'b0(raw)':>14}{'b0_identityA':>15}{'Sigma':>10}{'b0*tau':>11}{'2qtau/(1-q)':>13}")
for m in [1,2,4,8,16,32,48,64]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-math.log(q)
    b0,b1,t0,t1,L,v=raw_f(q,N)
    acc=0.0; S=[0.0]*(N+1)
    for a in range(N-1,0,-1):
        acc+=q**a*L[a]; S[a]=(1-q)*acc
    Sig=0.0
    for c in range(1,N): Sig+=S[c]*q**(c-1)
    b0_id=2*q/(1-q)+2*q*Sig
    print(f"{m:>3}{b0:>14.6f}{b0_id:>15.6f}{Sig:>10.6f}{b0*tau:>11.7f}{2*q*tau/(1-q):>13.7f}")

print("\nIDENTITY B (exact chain): t1 = u1[0] = v[0];  s=q/(1-q)*t1")
print("v1 -> -2/3 (travel-pole signature); v0 -> tau/4 ; s -> 1/4")
print(f"{'m':>3}{'t1(raw)':>14}{'v[0](raw)':>14}{'v1':>11}{'(v1+2/3)/tau':>14}{'v0/tau':>10}{'s=gV*t1':>10}")
for m in [1,2,4,8,16,32,48,64]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-math.log(q)
    b0,b1,t0,t1,L,v=raw_f(q,N)
    gV=q/(1-q)
    print(f"{m:>3}{t1:>14.8f}{v[0]:>14.8f}{v[1]:>11.6f}{(v[1]+2/3)/tau:>14.6f}{v[0]/tau:>10.6f}{gV*t1:>10.6f}")
print("\n  41/36 =",41/36,"  targets: v0/tau->1/4, s->1/4, b0*tau->2")
