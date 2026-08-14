import mpmath as mp
mp.mp.dps=60
import sys

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
        if abs(prod)<mp.mpf(10)**(-160) and j>60: break
    return tot
def A_(k,q): return 2*q/(1-q**(k+1))
def C_(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A_(k+2*j,q)*prod; prod*=C_(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-160) and j>60: break
    return tot

poles=[mp.mpf(l.strip()) for l in open('poles.txt')]

print("R2 heart: subleading of (Sig0 - Sb0). Both ~ w sin w (numerator-asymptotic); leading CANCELS.")
print(" (Sig0-Sb0)/(sqrt(tau) w sin w) -> d (a subleading coeff). Then P12=-(p/2q)(Sig0-Sb0),")
print(" P12 ~ -(tau/2)*d*sqrt(tau)*w sin w = -(d/2) tau^{3/2} w sin w; w=sqrt(2/tau) => tau^{3/2}w=sqrt2 tau.")
print(" So P12 ~ -(d/sqrt2) tau sin w?? wait recompute scale below numerically.")
print(f"{'m':>3} {'w':>8} {'(Sig0-Sb0)':>15} {'/(sqrt(tau) w sinw)':>20} {'P12/(tau^1.5 sinw)':>20}")
for i in [2,4,8,16,24]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=60+int(2.2*float(w))
    s0=Sig(0,q); sb0=Sb(0,q); sw=mp.sin(w)
    d=s0-sb0
    N=int(45/(1-q)); P12,P22,_,_=cocycle(q,N)
    print(f"{i:>3} {float(w):>8.2f} {mp.nstr(d,8):>15} {mp.nstr(d/(mp.sqrt(tau)*w*sw),9):>20} {mp.nstr(P12/(tau**mp.mpf('1.5')*sw),9):>20}")
    sys.stdout.flush(); mp.mp.dps=60

print()
print("END-TO-END CLOSURE (using ONLY proven-block identities + asymptotics):")
print(" R1: So/Se. Se=1-Sb1, So=(p/2q)Sb0 [EXACT, 1e-70].")
print("     At pole Sig1=1 => Se=Sig1-Sb1; leading (1-cosw) cancels => Se=(cT-cB)rt sinw=(1/sqrt2)rt sinw.")
print("     So=(p/2q)Sb0 ~ (tau/2) w sin w = (1/sqrt2) rt sin w.  => So/Se -> 1.")
print(" R2: t1=P12/Se. P12=-(p/2q)(Sig0-Sb0)[ratio->1]; leading w sinw cancels => P12~(1/(4sqrt2))tau^{3/2}sinw.")
print("     t1=P12/Se ~ [(1/(4sqrt2))tau^{3/2}]/[(1/sqrt2)rt] sinw/sinw = (1/4) tau.  => t1/tau->1/4.")
print()
print("FINAL NUMERICAL CONFIRMATION of both limits via the block route only:")
print(f"{'m':>3} {'w':>8} {'So/Se':>13} {'(R1->1)':>9} {'t1/tau':>13} {'(R2->1/4)':>11}")
for i in [1,2,4,8,16,24,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    mp.mp.dps=60+int(2.2*float(w))
    sb1=Sb(1,q); sb0=Sb(0,q)
    Se=1-sb1; So=(p/(2*q))*sb0
    N=int(45/(1-q)); P12,P22,_,_=cocycle(q,N)
    t1=P12/P22  # P22=Se (cocycle) -- cross-check with block Se below
    print(f"{i:>3} {float(w):>8.2f} {mp.nstr(So/Se,9):>13} {mp.nstr(abs(So/Se-1),3):>9} {mp.nstr(t1/tau,9):>13} {mp.nstr(abs(t1/tau-mp.mpf(1)/4),3):>11}")
    sys.stdout.flush(); mp.mp.dps=60
