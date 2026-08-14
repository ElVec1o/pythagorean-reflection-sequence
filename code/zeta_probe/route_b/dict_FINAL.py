import mpmath as mp
mp.mp.dps=70

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
def al(k,q): return 2*q**(k+1)/(1-q**(k+1))
def ga(k,q): return 2*q**(k+2)/(1-q**(k+2)) - 2*q**(k+1)/(1-q**(k+1))
def Sb(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=al(k+2*j,q)*prod; prod*=ga(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-170) and j>60: break
    return tot

print("="*100)
print("EXACT IDENTITIES (off-pole) verified to high precision:")
print("  (E1)  Se = 1 - S_1^bulk")
print("  (E2)  So = ((1-q)/(2q)) * S_0^bulk")
print("="*100)
print(f"{'q':>7} {'|Se-(1-S1blk)|':>16} {'|So-(p/2q)S0blk|':>18}")
for qf in ['0.8','0.85','0.9','0.93','0.95','0.97','0.99','0.995']:
    q=mp.mpf(qf); J=int(95/(1-q)); p=1-q
    Se,So=SeSo(q,J); sb1=Sb(1,q); sb0=Sb(0,q)
    e1=abs(Se-(1-sb1)); e2=abs(So-(p/(2*q))*sb0)
    print(f"{qf:>7} {mp.nstr(e1,4):>16} {mp.nstr(e2,4):>18}")

print()
print("CONSEQUENCE: So/Se = (1-q)/(2q) * S0blk / (1 - S1blk).")
print("Bulk asymptotics (lem:cos / numerator-asymptotic):  S1blk ~ 1-cos w,  S0blk ~ w sin w.")
print(" => 1-S1blk ~ cos w,  (p/2q)S0blk ~ (tau/2)*w sin w = (1/2)sqrt(2 tau) sin w  [since p~tau,w=sqrt(2/tau)]")
print(" Wait: (1-q)/(2q) ~ tau/2; (tau/2)*w sin w; tau*w = tau*sqrt(2/tau)=sqrt(2 tau). So So ~ (1/2)sqrt(2tau) sin w.")
print()
print("AT POLES: 1-S1blk -> 0 (since S1blk->1 by definition of pole? NO: poles are Sigma_1=1, not S1blk).")
print("Print at travel poles to confirm So/Se->1 via the EXACT bridge:")
poles=[mp.mpf(l.strip()) for l in open('poles.txt')]
print(f"{'m':>3} {'w':>8} {'1-S1blk(=Se)':>14} {'(p/2q)S0blk(=So)':>17} {'So/Se':>11} {'cos w':>10} {'(1/2)sqrt(2tau)sinw':>20}")
import sys
for i in [1,2,4,8,12,16,20,24,28,32]:
    if i>len(poles): break
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps = 60 + int(2.2*float(w))
    sb1=Sb(1,q); sb0=Sb(0,q)
    Se=1-sb1; So=(p/(2*q))*sb0
    print(f"{i:>3} {float(w):>8.2f} {mp.nstr(Se,7):>14} {mp.nstr(So,7):>17} {mp.nstr(So/Se,9):>11} {float(mp.cos(w)):>10.5f} {mp.nstr((p/(2*q))*w*mp.sin(w),8):>20}")
    sys.stdout.flush(); mp.mp.dps=70
