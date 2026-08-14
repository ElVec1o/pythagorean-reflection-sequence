import mpmath as mp
mp.mp.dps=40

def SeSo(q,J):
    p=1-q; poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    Se=sum((-2*p)**j*q**(j*(j+1))/poch[2*j] for j in range(J))
    So=sum((-2*p)**j*q**(j*(j+2))*p/poch[2*j+1] for j in range(J))
    return Se,So
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

print("HIGH-PRECISION test: Se =? 1 - S1_bulk   (and other bulk combos)")
print(f"{'q':>8} {'Se':>16} {'1-S1':>16} {'Se-(1-S1)':>12} {'So':>14} {'S0':>14} {'So-?':>12}")
for qf in ['0.85','0.9','0.93','0.97','0.99','0.995']:
    q=mp.mpf(qf); N=int(60/(1-q)); p=1-q; J=int(90/(1-q))
    Se,So=SeSo(q,J); b1=Sb(1,q);b0=Sb(0,q)
    print(f"{qf:>8} {mp.nstr(Se,11):>16} {mp.nstr(1-b1,11):>16} {mp.nstr(Se-(1-b1),5):>12} {mp.nstr(So,9):>14} {mp.nstr(b0,9):>14}")

print()
print("So vs bulk: try So =? combos. Look at So, S0, and So/S0 stability:")
print("Also test So =? -S0*(something). And test t1-related: P12 vs S0, Sig0.")
# So and S0 ratio was ~0.005 at q=0.99 for both Sig0 and S0 -- maybe So ~ S0 * p/something
print(f"{'q':>8} {'So':>14} {'S0':>14} {'So/S0':>12} {'So/(S0*p)':>14} {'So/(S0*p^2)':>14}")
for qf in ['0.85','0.9','0.95','0.99','0.997']:
    q=mp.mpf(qf); p=1-q; J=int(90/(1-q))
    Se,So=SeSo(q,J); b0=Sb(0,q)
    print(f"{qf:>8} {mp.nstr(So,9):>14} {mp.nstr(b0,9):>14} {mp.nstr(So/b0,7):>12} {mp.nstr(So/(b0*p),9):>14} {mp.nstr(So/(b0*p*p),9):>14}")
