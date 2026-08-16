import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<5:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("Fit A_b (bulk) to C1 cos(W u) + C2 sin(W u) + K, u=q^b, by least squares over W.")
print("Compare the best W with sqrt(2/tau) (the travel value) and with candidates.\n")
print("  m   tau        W_fit      sqrt(2/tau)   W_fit/sqrt(2/tau)   resid")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); tau=-mp.log(qm); wt=mp.sqrt(2/tau)
    P=bulk_solve(qm,mp.mpf(1),N)
    A=[mp.mpf(0)]*(N+2)
    for b in range(1,N+1): A[b+1]=A[b]+P[b]
    us=[]; ys=[]
    for b in range(1,N+1):
        u=qm**b
        if u<mp.mpf('0.02'): break
        us.append(u); ys.append(A[b])
    def resid(W):
        # least squares for C1,C2,K given W
        import itertools
        basis=[[mp.cos(W*u) for u in us],[mp.sin(W*u) for u in us],[mp.mpf(1)]*len(us)]
        G=mp.matrix(3,3); h=mp.matrix(3,1)
        for i in range(3):
            for j in range(3): G[i,j]=sum(basis[i][k]*basis[j][k] for k in range(len(us)))
            h[i]=sum(basis[i][k]*ys[k] for k in range(len(us)))
        try: c=mp.lu_solve(G,h)
        except Exception: return mp.mpf(1e18)
        r=mp.mpf(0)
        for k in range(len(us)):
            pr=c[0]*basis[0][k]+c[1]*basis[1][k]+c[2]
            r+=(pr-ys[k])**2
        return mp.sqrt(r/len(us))/max(abs(max(ys,key=abs)),mp.mpf(1))
    best=None
    W=wt*mp.mpf('0.5')
    while W<wt*mp.mpf('2.0'):
        r=resid(W)
        if best is None or r<best[1]: best=(W,r)
        W+=wt/mp.mpf(200)
    Wb,rb=best
    print(f"  {m}  {mp.nstr(tau,6):>9}  {mp.nstr(Wb,7):>9}  {mp.nstr(wt,7):>11}   {mp.nstr(Wb/wt,7):>12}   {mp.nstr(rb,4)}")
