import mpmath as mp
mp.mp.dps=30
def Sig1(q):
    tot=mp.mpf(0); prod=mp.mpf(1); j=0
    while True:
        k=1+2*j
        tot += 2*q/(1-q**(k+1))*prod
        prod *= 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(prod)<mp.mpf(10)**(-40) and j>30: break
        j+=1
        if j>50000: break
    return tot
def G(q,z,N=200):
    """1phi1(0;q;q^2,z) = sum_n (-1)^n q^{n(n-1)} z^n / ((q;q^2)_n (q^2;q^2)_n), built incrementally."""
    tot=mp.mpf(0); term=mp.mpf(1); p1=mp.mpf(1); p2=mp.mpf(1)
    q2=q*q
    for n in range(N):
        if n>0:
            p1*= (1-q*q2**(n-1))      # (q;q^2)_n
            p2*= (1-q2*q2**(n-1))     # (q^2;q^2)_n
        t=(-1)**n * q**(n*(n-1)) * z**n /(p1*p2)
        tot+=t
        if n>5 and abs(t)<mp.mpf(10)**(-45): break
    return tot
print('Test  1 - Sigma_1(q) = 1phi1(0;q;q^2, 2q(1-q))')
print('        q            1-Sigma_1              G(q,2q(1-q))          rel.diff')
for qq in ['0.2','0.35','0.449453630559','0.6','0.75','0.9134866387']:
    q=mp.mpf(qq); lhs=1-Sig1(q); rhs=G(q,2*q*(1-q))
    d=abs(lhs-rhs)/max(abs(lhs),mp.mpf('1e-25'))
    print(f'  {qq:>16}  {mp.nstr(lhs,12):>18}  {mp.nstr(rhs,12):>18}   {mp.nstr(d,4)}')
