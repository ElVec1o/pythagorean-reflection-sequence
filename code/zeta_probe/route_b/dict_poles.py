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

print("="*120)
print("AT TRAVEL POLES: verify the dictionary Se=1-S1bulk, So=S0bulk*p/(2q), and check b0,s limits")
print("="*120)
print(f"{'m':>3} {'w':>8} {'Se-(1-S1)':>12} {'So-S0p/2q':>12} {'b0*tau':>12} {'So/Se':>10} {'1-S1bulk':>11} {'(R1)So/Se->1':>12}")
for i in [1,2,4,8,16,32,64,80]:
    if i>len(poles): break
    q=poles[i-1]; N=int(80/(1-q)); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); J=int(8*w)+120
    Se,So=SeSo(q,J); P12,P22,_,_=cocycle(q,N); b1=Sb(1,q);b0bk=Sb(0,q)
    b0=(2*q/p)*So/Se
    print(f"{i:>3} {float(w):>8.3f} {mp.nstr(Se-(1-b1),4):>12} {mp.nstr(So-b0bk*p/(2*q),4):>12} {float(b0*tau):>12.8f} {float(So/Se):>10.7f} {float(1-b1):>11.7f} {float(So/Se):>12.7f}")

print()
print("KEY: at a travel pole Sigma_1(q_m)=1 (travel block). Does Se=1-S1bulk relate to Sigma_1?")
print("Note Se uses BULK S1, but the pole condition is on TRAVEL Sigma_1. Check both at poles:")
print(f"{'m':>3} {'w':>8} {'Sigma1_travel':>14} {'S1_bulk':>12} {'Se=1-S1bulk':>14} {'cos w':>10} {'1-cos w':>10}")
for i in [1,2,4,8,16,32,64,80]:
    if i>len(poles): break
    q=poles[i-1]; N=int(80/(1-q)); p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); J=int(8*w)+120
    Se,So=SeSo(q,J); b1=Sb(1,q)
    s1t=Sig(1,q)
    print(f"{i:>3} {float(w):>8.3f} {float(s1t):>14.9f} {float(b1):>12.8f} {float(Se):>14.9f} {float(mp.cos(w)):>10.6f} {float(1-mp.cos(w)):>10.6f}")
