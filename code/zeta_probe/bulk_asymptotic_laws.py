import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99985') and len(qs)<16:
    q2=min(q+step,mp.mpf('0.999855')); cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-28))
    q,prev=q2,cur
    if q>mp.mpf('0.99'):   step=mp.mpf('0.0001')
    if q>mp.mpf('0.998'):  step=mp.mpf('0.00002')
    if q>mp.mpf('0.9995'): step=mp.mpf('0.000004')
print(f"{len(qs)} poles.  FROZEN LAWS:  B_V/w^4 -> 2/3 = 0.666667 ;  |beta|/w -> 4/3 = 1.333333")
print("  m    B_V/w^4     pair-avg      |beta|/w    pair-avg     (out of sample from m=11)")
prevB=prevb=None
for m,qm in enumerate(qs,1):
    N=Nfor(qm); tau=-mp.log(qm); w=mp.sqrt(2/tau)
    P=bulk_solve(qm,mp.mpf(1),N)
    beta=sum(qm**k*P[k] for k in range(1,N+1)); BV=sum(P[1:])
    rB=BV/w**4; rb=abs(beta)/w
    pa = f"{mp.nstr((rB+prevB)/2,7):>10}" if prevB is not None else "         -"
    pb = f"{mp.nstr((rb+prevb)/2,7):>10}" if prevb is not None else "         -"
    tag = "  <-- out of sample" if m>=11 else ""
    print(f"  {m:2d}  {mp.nstr(rB,6):>9}  {pa}  {mp.nstr(rb,6):>10}  {pb}{tag}", flush=True)
    prevB, prevb = rB, rb
