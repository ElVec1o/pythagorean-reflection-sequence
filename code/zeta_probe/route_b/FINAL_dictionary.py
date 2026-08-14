import mpmath as mp
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
def Sb(k,q,J=60000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-180) and j>80: break
    return tot

poles=[l.strip() for l in open('poles.txt') if l.strip()]

print("="*100)
print("FINAL DICTIONARY (exact identities, verified at multiple precisions)")
print("="*100)
print(" Se = 1 - S1_bulk ;  So = S0_bulk*(1-q)/(2q) ;  b0=(2q/p)So/Se = S0/(1-S1) = B_V")
print(" Step links: C(k)=q*gamma(k) ; A(k)=q^{-k}*alpha(k) ; cocycle Wronskian x*Y-X*y=-1")
print()
print("Verify identities at travel poles (where both bulk Lambert & Pochhammer are computable):")
print(f"{'m':>3} {'w':>8} {'Se-(1-S1)':>13} {'So-S0p/2q':>13} {'b0-S0/(1-S1)':>14}")
for i in [1,2,4,8,16]:
    mp.mp.dps=60
    q=mp.mpf(poles[i-1]); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    J=int(float(w)**2/2)+200; N=int(150/float(p))
    Se,So=SeSo(q,J); b1=Sb(1,q); b0bk=Sb(0,q)
    b0=(2*q/p)*So/Se
    print(f"{i:>3} {float(w):>8.3f} {mp.nstr(Se-(1-b1),4):>13} {mp.nstr(So-b0bk*p/(2*q),4):>13} {mp.nstr(b0-b0bk/(1-b1),4):>14}")

print()
print("R1: So/Se -> 1  (rate (So/Se-1)/tau -> 1/2) ;  R2: t1/tau -> 1/4 (rate ->3/16) -- Pochhammer:")
print(f"{'m':>3} {'w':>9} {'So/Se':>13} {'(So/Se-1)/tau':>14} {'t1/tau':>13} {'(t1/tau-1/4)/tau':>16}")
for i in [1,4,16,32,64,80]:
    mp.mp.dps=int(float(mp.sqrt(2/(-mp.log(mp.mpf(poles[i-1])))))) *2+80
    q=mp.mpf(poles[i-1]); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau)
    J=int(float(w)**2/2)+200; N=int(150/float(p))
    Se,So=SeSo(q,J); P12,_,_,_=cocycle(q,N)
    r=So/Se; t1=P12/Se
    print(f"{i:>3} {float(w):>9.3f} {mp.nstr(r,9):>13} {mp.nstr((r-1)/tau,7):>14} {mp.nstr(t1/tau,9):>13} {mp.nstr((t1/tau-mp.mpf(1)/4)/tau,7):>16}")
