import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<4:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("bulk:  A_{b+2} = (1+q-2q^{1+2b}(1-q)) A_{b+1} - q A_b - 2 beta g q^{2b+1}(1-q)")
print("  m   max |residual|        max |A_b|")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); g=qm/(1-qm)
    P=bulk_solve(qm,mp.mpf(1),N)
    beta=sum(qm**k*P[k] for k in range(1,N+1))
    A=[mp.mpf(0)]*(N+3)
    for b in range(1,N+1): A[b+1]=A[b]+P[b]
    worst=mp.mpf(0)
    for b in range(1,N-2):
        p=1+qm-2*qm**(1+2*b)*(1-qm)
        src=-2*beta*g*qm**(2*b+1)*(1-qm)
        worst=max(worst, abs(A[b+2]-(p*A[b+1]-qm*A[b]+src)))
    print(f"  {m}   {mp.nstr(worst,6):>14}    {mp.nstr(max(abs(x) for x in A[:N]),8)}")
print()
print("Same p as travel with the index half-shifted, and a SINGLE geometric source term.")
