import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<4:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("Is the bulk really governed by eps A'' + A = -g beta ?")
print("Test: does the discrete bulk A_b satisfy the SECOND-ORDER relation, i.e. is")
print("eps A''(u) + A(u) constant in u (equal to -g beta) ?\n")
print("  m   w         g_V          beta=B_1        eps A''+A at u=0.3,0.5,0.7 (should be constant)")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); tau=-mp.log(qm); w=mp.sqrt(2/tau); eps=tau/2; g=qm/(1-qm)
    P=bulk_solve(qm,mp.mpf(1),N)
    A=[mp.mpf(0)]*(N+2)
    for b in range(1,N+1): A[b+1]=A[b]+P[b]
    beta=sum(qm**b*P[b] for b in range(1,N+1))
    # sample A as a function of u=q^b, estimate A'' by finite differences in u
    vals=[]
    for utar in (mp.mpf('0.3'),mp.mpf('0.5'),mp.mpf('0.7')):
        b=int(mp.log(utar)/mp.log(qm))
        if b<3 or b>N-3: vals.append(None); continue
        u=[qm**k for k in (b-1,b,b+1)]
        a=[A[k] for k in (b-1,b,b+1)]
        # non-uniform second difference in u
        h1=u[1]-u[0]; h2=u[2]-u[1]
        d2=2*(a[0]*h2 - a[1]*(h1+h2) + a[2]*h1)/(h1*h2*(h1+h2))
        vals.append(eps*d2+a[1])
    vs=" ".join(mp.nstr(v,7).rjust(12) if v is not None else "     n/a" for v in vals)
    print(f"  {m}  {mp.nstr(w,6):>8}  {mp.nstr(g,8):>10}  {mp.nstr(beta,8):>12}  {vs}   -g*beta={mp.nstr(-g*beta,7)}")
