import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.998') and len(qs)<8:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
    if q>mp.mpf('0.99'): step=mp.mpf('0.0002')
print("Continuum solution:  A(u)=Sigma_0 cos(w u),  R_s = tau w Sigma_0 u sin(w u),  u=q^s")
print("Predicted: nodes of R at u=k pi/w for k=1..m-1;  head = A(pi/w) = -Sigma_0.\n")
print("  m   w          nodes(obs)  nodes(pred)   A_s vs Sigma_0 cos(wu): max rel.err   head/(-Sigma_0)")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); tau=-mp.log(qm); w=mp.sqrt(2/tau)
    R,_=travel_null(qm,N); S0=sum(R)
    A=[mp.mpf(0)]*(N+1)
    for s in range(N): A[s+1]=A[s]+R[s]
    # compare A_s against Sigma_0 cos(w q^s) on the range where q^s is not tiny
    errs=[]
    for s in range(0,N):
        u=qm**s
        if u<mp.mpf('1e-3'): break
        pred=S0*mp.cos(w*u)
        errs.append(abs(A[s]-pred)/max(abs(S0),mp.mpf(1)))
    sgn=[1 if R[s]>0 else -1 for s in range(N)]
    nodes=[s for s in range(N-1) if sgn[s]*sgn[s+1]<0]
    last=nodes[-1] if nodes else -1
    head=sum(R[s] for s in range(last+1))
    print(f"  {m:2d}  {mp.nstr(w,7):>9}   {len(nodes):5d}      {m-1:5d}        {mp.nstr(max(errs),4):>10}"
          f"          {mp.nstr(head/(-S0),9)}")
