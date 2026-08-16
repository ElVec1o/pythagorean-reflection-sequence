import mpmath as mp
mp.mp.dps=30
def Sig(q,k):
    A=lambda j: 2*q/(1-q**(j+1))
    C=lambda j: 2*q**(j+3)/(1-q**(j+2)) - 2*q**(j+2)/(1-q**(j+1))
    tot=mp.mpf(0); prod=mp.mpf(1); j=0
    while True:
        tot+=A(k+2*j)*prod; prod*=C(k+2*j)
        if abs(prod)<mp.mpf(10)**(-mp.mp.dps-10) and j>30: break
        j+=1
        if j>300000: break
    return tot
def Nfor(q): return max(600,int(mp.ceil(40/(1-q))))
def travel_null(q,N):
    R=[mp.mpf(0)]*N; A=mp.mpf(0); B=mp.mpf(1)
    for s in range(N):
        r=2*q**(1+s)*(q**s*A+B); R[s]=r; A+=r; B-=q**s*r
    return R,B
def bulk_solve(q,y,N):
    g=q/(1-q*y)
    def run(beta):
        P=[mp.mpf(0)]*(N+1); A=mp.mpf(0); B=beta
        for b in range(1,N+1):
            p=2*q**b*(1+q**b*A+B+g*q**b*beta); P[b]=p; A+=p; B-=q**b*p
        return P,B
    P0,B0=run(mp.mpf(0)); P1,B1=run(mp.mpf(1))
    t=-B0/(B1-B0)
    return [P0[b]+t*(P1[b]-P0[b]) for b in range(N+1)]
def mu_vec(q,P,N):
    """O(N) via prefix sums:
       mu_s = 1/2 [ x^{2s+1}(C[s+1]+C[s]) + T1[s+2] + T2[s+1] ]
       C[k]=sum_{b<=k}P_b, T1[k]=sum_{b>=k}P_b x^{2b-1}, T2[k]=sum_{b>=k}P_b x^{2b+1}."""
    x=mp.sqrt(q)
    C=[mp.mpf(0)]*(N+2)
    for b in range(1,N+1): C[b]=C[b-1]+P[b]
    C[N+1]=C[N]
    T1=[mp.mpf(0)]*(N+3); T2=[mp.mpf(0)]*(N+3)
    for b in range(N,0,-1):
        T1[b]=T1[b+1]+P[b]*x**(2*b-1)
        T2[b]=T2[b+1]+P[b]*x**(2*b+1)
    mu=[mp.mpf(0)]*N
    for s in range(N):
        c1=C[min(s+1,N)]; c2=C[min(s,N)]
        mu[s]=(x**(2*s+1)*(c1+c2) + T1[min(s+2,N+1)] + T2[min(s+1,N+1)])/2
    return mu
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.9975') and len(qs)<9:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
    if q>mp.mpf('0.99'): step=mp.mpf('0.0002')
print(" m   q_m            Sigma_0(q_m)     <lam,R>          <L,mu>           Pi              sign")
for m,qm in enumerate(qs,1):
    N=Nfor(qm)
    R,res=travel_null(qm,N); P=bulk_solve(qm,mp.mpf(1),N); mu=mu_vec(qm,P,N)
    lam=mu
    lr=sum(lam[s]*R[s] for s in range(N))
    lm=sum(R[s]/(2*qm**(1+s))*mu[s] for s in range(N))
    Pi=lr*lm; S0=Sig(qm,0)
    print(f" {m:2d}  {mp.nstr(qm,10):>12}  {mp.nstr(S0,8):>13}  {mp.nstr(lr,8):>14}  {mp.nstr(lm,8):>14}  {mp.nstr(Pi,8):>14}   {'+' if Pi>0 else '-'}")
