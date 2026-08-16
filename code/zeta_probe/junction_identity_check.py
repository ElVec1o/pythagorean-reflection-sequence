import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.985') and len(qs)<4:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("Check the paper's identity  <lam,R> = x*B + sum_sigma (B_sigma/2)(Delta^+ + Delta^-)")
print("with Delta_sigma^pm = sum_{2s+1 < sigma -+ 1} ( x^{sigma -+ 1} - x q^s ) R_s,")
print("which uses sum_s q^s R_s = Sigma_1(q_m) = 1.\n")
print("  m   sum q^s R_s   <lam,R> direct   x*B + corrections   rel.diff")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); x=mp.sqrt(qm)
    R,_=travel_null(qm,N); P=bulk_solve(qm,mp.mpf(1),N); mu=mu_vec(qm,P,N)
    norm=sum(qm**s*R[s] for s in range(N))
    direct=sum(mu[s]*R[s] for s in range(N))
    B=sum(P[1:])
    corr=mp.mpf(0)
    for b in range(1,min(N,400)+1):
        pb=P[b]
        if pb==0: continue
        for sgn in (-1,1):                 # sigma -+ 1 with sigma = 2b
            e=2*b+sgn
            d=mp.mpf(0)
            smax=(e-1)//2                  # 2s+1 < e  <=>  s < (e-1)/2
            for s in range(0,smax):
                d+= (x**e - x*qm**s)*R[s]
            corr += (pb/2)*d
    pred=x*B+corr
    rel=abs(direct-pred)/max(abs(direct),mp.mpf(1))
    print(f"  {m}   {mp.nstr(norm,8):>11}  {mp.nstr(direct,9):>14}  {mp.nstr(pred,9):>16}   {mp.nstr(rel,4)}")
