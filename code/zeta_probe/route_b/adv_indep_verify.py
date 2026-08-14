import mpmath as mp

# ---- raw resolvent (b0,b1,t0,t1) + L array ----
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

def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p

# ---- Se, So from exact closed forms ----
def Se_So(q,Jmax):
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0)
    for j in range(0,Jmax):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te; So+=to
    return Se,So

# ---- travel block Sigma_k and bulk block Sbulk_k ----
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>40: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sbulk(k,q,J):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-5) and j>40: break
    return tot

polestr=[l.strip() for l in open("poles.txt") if l.strip()]

# ================ PART 1: off-pole exact identities E1, E2 ================
print("="*100)
print("PART 1  off-pole exact identities (high dps)")
print(" E1: Se = 1 - S1_bulk    E2(report): So = ((1-q)/(2q)) * S0_bulk    E2(verify_E1E2): So*Sigma0=1")
print("="*100)
mp.mp.dps=60
print(f"{'q':>6} | {'|Se-(1-S1b)|':>13} | {'|So-(p/2q)S0b|':>15} | {'|So*Sig0-1|':>13} | {'t1=P12/Se chk':>14}")
for qv in ['0.5','0.7','0.8','0.85','0.9','0.95']:
    q=mp.mpf(qv); N=int(80/(1-q)); J=int(6/(1-q))+200
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q,J)
    S1b=Sbulk(1,q,4000); S0b=Sbulk(0,q,4000); Sig0=Sigma(0,q,4000)
    p=1-q
    e1=abs(Se-(1-S1b))
    e2r=abs(So-(p/(2*q))*S0b)
    e2v=abs(So*Sig0-1)
    # t1 = P12/Se where P12=t1*Se by def? check the closed form b0=(2q/p)*So/Se
    b0chk=abs(b0-(2*q/p)*So/Se)
    print(f"{qv:>6} | {mp.nstr(e1,3):>13} | {mp.nstr(e2r,3):>15} | {mp.nstr(e2v,3):>13} | b0id={mp.nstr(b0chk,3)}")

print()
print("Cross-check the TWO E2 claims are consistent: is (p/2q)*S0b == 1/Sigma0 ?")
for qv in ['0.7','0.85','0.95']:
    q=mp.mpf(qv); S0b=Sbulk(0,q,4000); Sig0=Sigma(0,q,4000); p=1-q
    lhs=(p/(2*q))*S0b; rhs=1/Sig0
    print(f"  q={qv}: (p/2q)S0b={mp.nstr(lhs,8)}  1/Sig0={mp.nstr(rhs,8)}  equal? {mp.nstr(abs(lhs-rhs),3)}")
