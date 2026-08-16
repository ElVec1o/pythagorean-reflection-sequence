import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.995') and len(qs)<6:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
    if q>mp.mpf('0.99'): step=mp.mpf('0.0002')
print("continuum prediction:  P = H_inf ~ -w^2 = -2/tau ,  beta ~ -1 ,  B_V ~ -1/tau")
print()
print("  m   tau        w=sqrt(2/tau)   beta(true)     P=B_V+beta g   -w^2        B_V(true)   -1/tau")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); g=qm/(1-qm); tau=-mp.log(qm); w=mp.sqrt(2/tau)
    P=bulk_solve(qm,mp.mpf(1),N)
    beta=sum(qm**k*P[k] for k in range(1,N+1))
    BV=sum(P[1:])
    print(f"  {m}  {mp.nstr(tau,6):>9}  {mp.nstr(w,6):>10}  {mp.nstr(beta,7):>12}  "
          f"{mp.nstr(BV+beta*g,7):>12}  {mp.nstr(-w**2,7):>10}  {mp.nstr(BV,7):>10}  {mp.nstr(-1/tau,7)}")
