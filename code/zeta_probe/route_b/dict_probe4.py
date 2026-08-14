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
def alpha(k,q): return 2*q**(k+1)/(1-q**(k+1))
def gamma(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=8000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-90) and j>50: break
    return tot

print("CONFIRM: b0 = (2q/p)*So/Se = S0/(1-S1) = B_V  (bulk resolvent identity)")
print(f"{'q':>8} {'(2q/p)So/Se':>18} {'S0/(1-S1)':>18} {'diff':>12}")
for qf in ['0.85','0.9','0.95','0.99']:
    q=mp.mpf(qf); p=1-q; J=int(90/(1-q))
    Se,So=SeSo(q,J); b1=Sb(1,q);b0=Sb(0,q)
    lhs=(2*q/p)*So/Se; rhs=b0/(1-b1)
    print(f"{qf:>8} {mp.nstr(lhs,13):>18} {mp.nstr(rhs,13):>18} {mp.nstr(lhs-rhs,5):>12}")

print()
print("Now P12 / t1. t1=P12/Se. Identify P12 in terms of bulk blocks.")
print("Candidates: P12 =? S0-related, or P12 =? function of S0,S1.")
print(f"{'q':>8} {'P12':>16} {'S0':>14} {'S1':>14} {'P12/S0':>12} {'P12/(1-S1)':>12} {'P12/(S0*p)':>12}")
for qf in ['0.85','0.9','0.95','0.99','0.997']:
    q=mp.mpf(qf); N=int(80/(1-q)); p=1-q; J=int(120/(1-q))
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N); b1=Sb(1,q);b0=Sb(0,q)
    print(f"{qf:>8} {mp.nstr(P12,9):>16} {mp.nstr(b0,8):>14} {mp.nstr(b1,8):>14} {mp.nstr(P12/b0,7):>12} {mp.nstr(P12/(1-b1),7):>12} {mp.nstr(P12/(b0*p),7):>12}")

print()
print("t1 = P12/Se. s = (q/p)*t1. Test t1 in terms of bulk: t1 =? combos")
print(f"{'q':>8} {'t1':>16} {'S0/(1-S1)*?':>14} {'b0=S0/(1-S1)':>16} {'t1/b0':>12} {'t1*2':>12}")
for qf in ['0.85','0.9','0.95','0.99']:
    q=mp.mpf(qf); N=int(80/(1-q)); p=1-q; J=int(120/(1-q))
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N); b1=Sb(1,q);b0=Sb(0,q)
    t1=P12/Se; B_V=b0/(1-b1)
    print(f"{qf:>8} {mp.nstr(t1,9):>16} {'':>14} {mp.nstr(B_V,11):>16} {mp.nstr(t1/B_V,7):>12} {mp.nstr(t1*2,7):>12}")
