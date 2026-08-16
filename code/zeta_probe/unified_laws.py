import mpmath as mp
mp.mp.dps=50
src=open('junction_pairing.py').read().split('f=lambda q')[0]
exec(src)
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99995') and len(qs)<14:
    q2=min(q+step,mp.mpf('0.999955')); cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-15))
    q,prev=q2,cur
    if q>mp.mpf('0.99'):   step=mp.mpf('0.0001')
    if q>mp.mpf('0.998'):  step=mp.mpf('0.00002')
    if q>mp.mpf('0.9995'): step=mp.mpf('0.000004')
print("Unified form.  w_m = (m-1/2)pi, so (pi/2)m - pi/4 = w/2 exactly.")
print("  m    w        w_meas=sqrt(2/tau)  (m-1/2)pi   ratio/(w/2)  Sigma_0/w   beta/Sigma_0")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); x=mp.sqrt(qm); tau=-mp.log(qm); w=mp.sqrt(2/tau); wq=(m-mp.mpf(1)/2)*mp.pi
    R,res=travel_null(qm,N); P=bulk_solve(qm,mp.mpf(1),N); mu=mu_vec(qm,P,N)
    lr=sum(mu[s]*R[s] for s in range(N)); B=sum(P[1:]); C=lr-x*B
    beta=sum(qm**k*P[k] for k in range(1,N+1)); S0=Sig(qm,0)
    print(f"  {m:2d} {mp.nstr(w,6):>8}  {mp.nstr(wq,6):>14}  {mp.nstr(abs(C)/(x*B)/(w/2),6):>10}  "
          f"{mp.nstr(S0/w,6):>10}  {mp.nstr(beta/S0,6):>10}", flush=True)
