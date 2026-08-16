import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.9985') and len(qs)<14:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
    if q>mp.mpf('0.99'): step=mp.mpf('0.0001')
print(" m  nodes  head/(-Sigma0)   S1 ok   |C_lam|/(xB)   S2 ok   Pi>0")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); x=mp.sqrt(qm)
    R,_=travel_null(qm,N); P=bulk_solve(qm,mp.mpf(1),N); mu=mu_vec(qm,P,N)
    S0=sum(R)
    sgn=[1 if R[s]>0 else -1 for s in range(N)]
    nodes=[s for s in range(N-1) if sgn[s]*sgn[s+1]<0]
    last=nodes[-1] if nodes else -1
    head=sum(R[s] for s in range(last+1))
    lr=sum(mu[s]*R[s] for s in range(N))
    lm=sum(R[s]/(2*qm**(1+s))*mu[s] for s in range(N))
    B=sum(P[1:]); C=lr-x*B
    s1 = (head*S0 < 0)                      # head sign opposite to Sigma_0
    s2 = abs(C) > x*B
    print(f" {m:2d}   {len(nodes):3d}   {mp.nstr(head/(-S0),7):>13}   {str(s1):>5}   "
          f"{mp.nstr(abs(C)/(x*B),7):>11}   {str(s2):>5}   {lr*lm>0}")
