import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<5:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("sign structure of R_s and positivity of the weight vectors")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); R,_=travel_null(qm,N); P=bulk_solve(qm,mp.mpf(1),N); mu=mu_vec(qm,P,N)
    Pneg=sum(1 for b in range(1,N+1) if P[b]<0)
    muneg=sum(1 for s in range(N) if mu[s]<0)
    sgn=[1 if R[s]>0 else (-1 if R[s]<0 else 0) for s in range(N)]
    flips=sum(1 for s in range(N-1) if sgn[s]*sgn[s+1]<0)
    # last sign change index, and tail sign
    last=max([s for s in range(N-1) if sgn[s]*sgn[s+1]<0], default=-1)
    # how much mass is in the tail after the last flip
    tail=sum(R[s] for s in range(last+1,N)); head=sum(R[s] for s in range(last+1))
    print(f" m={m}  N={N}  P_b<0 count={Pneg}  mu_s<0 count={muneg}  "
          f"R sign flips={flips}  last flip at s={last}")
    print(f"        head sum={mp.nstr(head,6)}  tail sum={mp.nstr(tail,6)}  "
          f"tail sign={'+' if tail>0 else '-'}  total={mp.nstr(head+tail,6)}")
