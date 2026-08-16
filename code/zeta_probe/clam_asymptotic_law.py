import mpmath as mp
mp.mp.dps=50
src=open('junction_pairing.py').read().split('f=lambda q')[0]
exec(src)
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.9999') and len(qs)<20:
    q2=min(q+step,mp.mpf('0.9999955')); cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-15))
    q,prev=q2,cur
    if q>mp.mpf('0.99'):   step=mp.mpf('0.0001')
    if q>mp.mpf('0.998'):  step=mp.mpf('0.00002')
    if q>mp.mpf('0.9995'): step=mp.mpf('0.000004')
    if q>mp.mpf('0.99995'): step=mp.mpf('0.0000004')
print(f"{len(qs)} poles.  FROZEN: ratio/m -> pi/2 = 1.5707963 ; ratio-(pi/2)m -> -pi/4 = -0.7853982")
print("  (frozen on m<=14; m>=15 is OUT OF SAMPLE)")
print("  m     ratio |C|/(xB)   ratio/m    pair-avg     ratio-(pi/2)m   pair-avg")
pr=pc=None
for m,qm in enumerate(qs,1):
    N=Nfor(qm); x=mp.sqrt(qm)
    R,res=travel_null(qm,N); P=bulk_solve(qm,mp.mpf(1),N); mu=mu_vec(qm,P,N)
    lam=mu
    lr=sum(lam[s]*R[s] for s in range(N))
    B=sum(P[1:])
    C=lr-x*B
    ratio=abs(C)/(x*B)
    rm=ratio/m; off=ratio-mp.pi/2*m
    pa=f"{mp.nstr((rm+pr)/2,7):>10}" if pr is not None else "         -"
    pb=f"{mp.nstr((off+pc)/2,7):>10}" if pc is not None else "         -"
    print(f"  {m:2d}  {mp.nstr(ratio,8):>14}  {mp.nstr(rm,6):>9}  {pa}  {mp.nstr(off,6):>12}  {pb}{'   <-- OOS' if m>=15 else ''}", flush=True)
    pr,pc=rm,off
