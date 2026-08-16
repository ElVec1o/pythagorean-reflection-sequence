import mpmath as mp
exec(open('/private/tmp/claude-501/-Users-vico-Documents-elvec1o-XXXXX-MATH-PROOF/600297f0-1b03-4b2c-8747-bbf6af9b3120/scratchpad/pi3.py').read().split('f=lambda q')[0])
f=lambda q: 1-Sig(q,1)
qs=[]; q=mp.mpf('0.05'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.995') and len(qs)<6:
    q2=q+step; cur=f(q2)
    if prev*cur<0: qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-25))
    q,prev=q2,cur
    if q>mp.mpf('0.99'): step=mp.mpf('0.0002')
print("Is B_V governed by the derivative of 1-Sigma_1 at the pole?")
print("  m   q_m          f'(q_m)          B_V            B_V*f'(q_m)      B_V*f'*(1-q)")
for m,qm in enumerate(qs,1):
    N=Nfor(qm)
    P=bulk_solve(qm,mp.mpf(1),N); BV=sum(P[1:])
    h=mp.mpf(10)**-12
    fp=(f(qm+h)-f(qm-h))/(2*h)
    print(f"  {m:2d}  {mp.nstr(qm,9):>11}  {mp.nstr(fp,9):>14}  {mp.nstr(BV,9):>12}  "
          f"{mp.nstr(BV*fp,9):>14}  {mp.nstr(BV*fp*(1-qm),9)}")
print()
print("Casoratian: for A_{s+2} = p_s A_{s+1} - q A_s, two solutions give W_{s+1} = q W_s,")
print("so W_s = q^s W_0 exactly.  That is the Green's-function ingredient for (S2).")
