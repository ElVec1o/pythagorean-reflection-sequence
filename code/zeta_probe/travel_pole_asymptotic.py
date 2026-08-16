import mpmath as mp
mp.mp.dps=40
def Sig1(q):
    tot=mp.mpf(0); prod=mp.mpf(1); j=0
    while True:
        k=1+2*j
        tot += 2*q/(1-q**(k+1))*prod
        prod *= 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(prod)<mp.mpf(10)**(-52) and j>30: break
        j+=1
        if j>200000: break
    return tot
f=lambda q: 1-Sig1(q)
# bracket successive zeros in (0,1)
qs=[]; q=mp.mpf('0.01'); prev=f(q); step=mp.mpf('0.002')
while q<mp.mpf('0.9995') and len(qs)<26:
    q2=q+step; 
    try: cur=f(q2)
    except Exception: break
    if prev*cur<0:
        qs.append(mp.findroot(f,(q,q2),solver='bisect',tol=mp.mpf(10)**-30))
    q, prev = q2, cur
    if q>mp.mpf('0.99'): step=mp.mpf('0.0002')
    if q>mp.mpf('0.999'): step=mp.mpf('0.00002')
print(f"{len(qs)} travel poles found")
tot=mp.mpf(0)
print(" m   q_m                 tau_m=-ln q_m     m^2*tau_m    sum(1-q_m)")
for i,qm in enumerate(qs,1):
    tau=-mp.log(qm); tot+=1-qm
    print(f"{i:3d}  {mp.nstr(qm,12):>14}  {mp.nstr(tau,8):>14}  {mp.nstr(i*i*tau,8):>10}  {mp.nstr(tot,8)}")
print("\nIf m^2*tau_m tends to a constant then 1-q_m ~ C/m^2 and sum(1-q_m) CONVERGES,")
print("so the Blaschke condition is satisfied and a vanishing numerator is NOT forced.")
