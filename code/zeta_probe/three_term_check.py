import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<4:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("Check A_{s+2} = (1+q-2q^{2+2s}(1-q)) A_{s+1} - q A_s on the exact travel data.")
print("  m   max |residual| over s        max |A_s|")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); R,_=travel_null(qm,N)
    A=[mp.mpf(0)]*(N+2)
    for s in range(N): A[s+1]=A[s]+R[s]
    worst=mp.mpf(0)
    for s in range(0,N-2):
        p=1+qm-2*qm**(2+2*s)*(1-qm)
        worst=max(worst, abs(A[s+2]-(p*A[s+1]-qm*A[s])))
    print(f"  {m}   {mp.nstr(worst,6):>16}      {mp.nstr(max(abs(x) for x in A[:N]),6)}")
print()
print("Also: the limit of A is Sigma_0, and the recursion's characteristic roots at")
print("s -> infinity are 1 and q.")
