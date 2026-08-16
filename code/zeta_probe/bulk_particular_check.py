import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.99') and len(qs)<4:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
print("Claim: H_b := A^bulk_b + beta*g satisfies the HOMOGENEOUS three-term recursion")
print("       H_{b+2} = (1+q-2q^{1+2b}(1-q)) H_{b+1} - q H_b   (no source)")
print()
print("  m   max |homogeneous residual|   max |H_b|      B_V            A_inf + beta g")
for m,qm in enumerate(qs,1):
    N=Nfor(qm); g=qm/(1-qm)
    P=bulk_solve(qm,mp.mpf(1),N)
    beta=sum(qm**k*P[k] for k in range(1,N+1))
    A=[mp.mpf(0)]*(N+3)
    for b in range(1,N+1): A[b+1]=A[b]+P[b]
    H=[A[b]+beta*g for b in range(N+3)]
    worst=mp.mpf(0)
    for b in range(1,N-2):
        p=1+qm-2*qm**(1+2*b)*(1-qm)
        worst=max(worst, abs(H[b+2]-(p*H[b+1]-qm*H[b])))
    BV=sum(P[1:])
    print(f"  {m}   {mp.nstr(worst,6):>18}   {mp.nstr(max(abs(x) for x in H[:N]),7):>10}   "
          f"{mp.nstr(BV,8):>11}   {mp.nstr(BV+beta*g,8)}")
print()
print("H_1 = A_1 + beta g = beta g  (since A_1 = 0), and H_inf = B_V + beta g.")
