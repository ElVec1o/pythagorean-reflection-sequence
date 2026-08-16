import mpmath as mp
mp.mp.dps=40
src=open('junction_pairing.py').read().split('f=lambda q')[0]
exec(src)
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.9999') and len(qs)<12:
    q2=min(q+step,mp.mpf('0.99991')); cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-15))
    q,prev=q2,cur
    if q>mp.mpf('0.99'):   step=mp.mpf('0.0001')
    if q>mp.mpf('0.998'):  step=mp.mpf('0.00002')
    if q>mp.mpf('0.9995'): step=mp.mpf('0.000004')
print("(S1): split R at its LAST sign change.  head = sum before, tail = sum after.")
print("  m  nodes  head/(-Sigma_0)   tail/Sigma_0   pair-avg(tail/S0)")
pt=None
for m,qm in enumerate(qs,1):
    N=Nfor(qm)
    R,res=travel_null(qm,N); S0=Sig(qm,0)
    sgn=[1 if x>0 else (-1 if x<0 else 0) for x in R]
    ch=[s for s in range(1,N) if sgn[s]!=0 and sgn[s-1]!=0 and sgn[s]!=sgn[s-1]]
    nodes=len(ch)
    if not ch:
        print(f"  {m:2d}  {nodes:4d}   (no sign change)"); continue
    last=ch[-1]
    head=sum(R[:last]); tail=sum(R[last:])
    ts=tail/S0
    pa=f"{mp.nstr((ts+pt)/2,8):>12}" if pt is not None else "           -"
    print(f"  {m:2d}  {nodes:4d}   {mp.nstr(head/(-S0),8):>14}   {mp.nstr(ts,8):>12}   {pa}", flush=True)
    pt=ts
