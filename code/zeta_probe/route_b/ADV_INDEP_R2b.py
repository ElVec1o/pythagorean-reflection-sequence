"""
Independent R2 verification, with the cocycle convention pinned so that P22=Se.
Tracks the two columns of the convA cocycle forward as 2-vectors.
P22-column: start (y0,y1)=(1, 1-2q^2) per memory -> this is Se.
P12-column: start (0, 2q^3) -> this is P12.
Then check E1 (P21=-S0b), E2 (unimod P11*Se+P12*S0b=1), E3 (t1=D/(S0b Se)),
and the R2 reduction t1 -> tau/4 at travel poles.
"""
import mpmath as mp

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
    return l0,l1,u0[0],u1[0]

def scalar_recur(q,N,y0,y1):
    # colleague's exact scalar 3-term: y_{n+1}=(1+q^3-2(1-q)q^{2n+2})y_n - q^3 y_{n-1}
    # indices: y0=y_0, y1=y_1; iterate to y_N. Return (y_{N-1},y_N) ~ converged value y_N.
    q=mp.mpf(q); q3=q**3; ym=mp.mpf(y0); yc=mp.mpf(y1)
    for n in range(1,N):
        coef=1+q3-2*(1-q)*q**(2*n+2)
        yn=coef*yc-q3*ym
        ym,yc=yc,yn
    return yc

def bulk_blocks(q,K=None):
    if K is None: K=int(10*mp.sqrt(2/(-mp.log(q))))+200
    def alpha(k): return 2*q**(k+1)/(1-q**(k+1))
    def gamma(k): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
    def Sb(start):
        tot=mp.mpf(0); prod=mp.mpf(1)
        for j in range(K):
            tot+=alpha(start+2*j)*prod
            prod*=gamma(start+2*j)
        return tot
    return Sb(0),Sb(1)

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# First: pin the scalar-recursion convention reproduces Se and P12.
print("=== Pin scalar recursion: Se=(1,1-2q^2) sol, P12=(0,2q^3) sol ===")
for qv in [0.75,0.85,0.93]:
    mp.mp.dps=70
    q=mp.mpf(qv); N=int(120/(1-q))
    b0,b1,t0,t1=raw(q,N)
    S0b,S1b=bulk_blocks(q)
    Se_block=1-S1b
    Se_rec=scalar_recur(q,N+1,1,1-2*q**2)
    P12_rec=scalar_recur(q,N+1,0,2*q**3)
    print(f"q={qv}: Se_rec-(1-S1b)={float(Se_rec-Se_block):.2e}  t1-P12_rec/Se_rec={float(t1-P12_rec/Se_rec):.2e}")
    # E3 using blocks: D=P12*S0b ; t1 = D/(S0b*Se)
    D=P12_rec*S0b
    print(f"      t1-(P12_rec*S0b)/(S0b*(1-S1b))={float(t1-D/(S0b*Se_block)):.2e}  [E3]")

print("\n=== R2 at travel poles: convergence of t1/tau -> 1/4, with diagnostics ===")
print(f"{'m':>3} {'tau':>9} {'t1/tau':>11} {'P12*S0b/tau':>12} {'S0b*Se':>9} {'P12/tau^1.5':>12} {'sinw/(4rt2)':>12}")
for m in [1,2,4,8,16,24,32,40,50,60]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.5*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(70/(1-q))
    b0,b1,t0,t1=raw(q,N)
    S0b,S1b=bulk_blocks(q)
    Se=1-S1b
    P12=scalar_recur(q,N+1,0,2*q**3)
    sinw=mp.sin(w)
    print(f"{m:>3} {float(tau):>9.2e} {float(t1/tau):>11.7f} {float(P12*S0b/tau):>12.7f} {float(S0b*Se):>9.6f} {float(P12/tau**mp.mpf('1.5')):>12.7f} {float(sinw/(4*mp.sqrt(2))):>12.7f}")
