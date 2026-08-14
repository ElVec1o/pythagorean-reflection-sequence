"""
Fully independent adversarial verification of the colleague's R2 claims.
Builds: raw(), cocycle (convA), bulk blocks S0b/S1b from alpha/gamma directly,
Se/So from Pochhammer. Cross-checks every dictionary entry and the R2 reduction.
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
    return l0,l1,u0[0],u1[0]   # b0,b1,t0,t1

def cocycle_full(q,N):
    # convA matrix M_n = [[1+2q^{2n}, -2q^n],[2q^{3n}, 1-2q^{2n}]]
    # accumulate product M_N ... M_1 applied to track all 4 entries.
    # Track columns: col1=(P11,P21) start (1,0); col2=(P12,P22) start (0,1).
    P11=mp.mpf(1); P21=mp.mpf(0); P12=mp.mpf(0); P22=mp.mpf(1)
    qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q; q2n=qn*qn; q3n=q2n*qn
        a=1+2*q2n; b=-2*qn; c=2*q3n; d=1-2*q2n
        nP11=a*P11+b*P21; nP21=c*P11+d*P21
        nP12=a*P12+b*P22; nP22=c*P12+d*P22
        P11,P21,P12,P22=nP11,nP21,nP12,nP22
    return P11,P12,P21,P22

def bulk_blocks(q,K=None):
    # alpha(k)=2 q^{k+1}/(1-q^{k+1}); gamma(k)=2 q^{k+2}/(1-q^{k+2})-2 q^{k+1}/(1-q^{k+1})
    # S1b=Sb(1): sum_j alpha(1+2j) prod_{i<j} gamma(1+2i)
    # S0b=Sb(0): sum_j alpha(0+2j) prod_{i<j} gamma(0+2i)
    if K is None: K=int(10*mp.sqrt(2/(-mp.log(q))))+200
    def alpha(k): return 2*q**(k+1)/(1-q**(k+1))
    def gamma(k): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
    def Sb(start):
        tot=mp.mpf(0); prod=mp.mpf(1)
        for j in range(K):
            k=start+2*j
            tot+=alpha(k)*prod
            prod*=gamma(start+2*j)
        return tot
    return Sb(0),Sb(1)   # S0b, S1b

def Se_So(q,J=None):
    if J is None: J=int(8*mp.sqrt(2/(-mp.log(q))))+200
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0); poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J):
        Se+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
        So+=(-2*onem)**j*q**(j*(j+2))*onem/poch[2*j+1]
    return Se,So

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("=== GENERIC q: dictionary identity cross-checks ===")
for qv in [0.75,0.85,0.93]:
    mp.mp.dps=60
    q=mp.mpf(qv); tau=-mp.log(q); p=1-q; N=int(80/(1-q))
    b0,b1,t0,t1=raw(q,N)
    P11,P12,P21,P22=cocycle_full(q,N)
    S0b,S1b=bulk_blocks(q)
    Se,So=Se_So(q)
    # D1: Se = 1 - S1b ;  also P22 should equal Se
    print(f"\nq={qv}  tau={float(tau):.4f}  N={N}")
    print(f"  P22 - Se(Pochhammer)        : {float(P22-Se):.2e}")
    print(f"  (1-S1b) - Se                : {float((1-S1b)-Se):.2e}   [D1]")
    print(f"  So - (p/2q)S0b              : {float(So-(p/(2*q))*S0b):.2e}   [D3]")
    print(f"  b0 - S0b/(1-S1b)            : {float(b0-S0b/(1-S1b)):.2e}   [D4]")
    print(f"  b1 - S1b/(1-S1b)            : {float(b1-S1b/(1-S1b)):.2e}   [D2 b1]")
    print(f"  t0 - S1b/(1-S1b)            : {float(t0-S1b/(1-S1b)):.2e}   [D2 t0]")
    print(f"  t1 - P12/Se                 : {float(t1-P12/Se):.2e}   [D5]")
    print(f"  P21 + S0b                   : {float(P21+S0b):.2e}   [E1]")
    print(f"  P11*Se + P12*S0b - 1        : {float(P11*Se+P12*S0b-1):.2e}   [E2 unimod]")
    # E3: t1 = D/(S0b*Se), D=P12*S0b=1-P11*Se
    D=1-P11*Se
    print(f"  D - P12*S0b                 : {float(D-P12*S0b):.2e}   [E2 D defn]")
    print(f"  t1 - D/(S0b*Se)             : {float(t1-D/(S0b*Se)):.2e}   [E3]")
    # det of full cocycle = 1 ?
    print(f"  det(P) - 1                  : {float(P11*P22-P12*P21-1):.2e}   [unimodular]")
