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

print("="*100)
print("CLOSURE CHECK 1: Se(q_m) = cos w_m - (Sb1-(1-cosw)).  Since at pole cos w_m is pinned by Sigma_1=1,")
print("  and Se=1-Sb1 EXACT, the whole thing is determined by BULK Sb1 and TRAVEL Sig1=1.")
print("  Identity Se = (1-Sig1) + (Sig1 - Sb1) = 0 + (Sig1-Sb1) at pole (Sig1=1).  So Se(q_m)=Sig1-Sb1 |_{pole}.")
print("="*100)
print(f"{'m':>3} {'w':>8} {'Se':>15} {'Sig1-Sb1':>15} {'diff':>10}")
for i in [2,4,8,16,24,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.2*float(w))
    sb1=Sb(1,q); s1=Sig(1,q)
    Se=1-sb1
    print(f"{i:>3} {float(w):>8.2f} {mp.nstr(Se,9):>15} {mp.nstr(s1-sb1,9):>15} {mp.nstr(Se-(s1-sb1),3):>10}")
    sys.stdout.flush(); mp.mp.dps=60

print()
print("="*100)
print("CLOSURE CHECK 2 (the heart): Se(q_m) = Sig1(q_m)-Sb1(q_m), and at pole Sig1=1.")
print(" Both Sig1 and Sb1 ~ (1-cos w) + c*sqrt(tau)*sin w.  Their leading (1-cos w) CANCELS in Sig1-Sb1!")
print(" => Se(q_m) = (c_T - c_B) sqrt(tau) sin w + O(tau), c_T=travel sub, c_B=bulk sub.")
print(" Measure c_T and c_B SEPARATELY via the SAME engine (both are lem:cos-class):")
print(f"{'m':>3} {'(1-cosw-Sb1)/(rt sinw)=cB':>26} {'(1-cosw-Sig1)/(rt sinw)=cT':>28} {'cB-cT':>12} {'-(1/sqrt2)':>12}")
for i in [2,4,8,16,24,32]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(2.2*float(w))
    sb1=Sb(1,q); s1=Sig(1,q); sw=mp.sin(w); cw=mp.cos(w); rt=mp.sqrt(tau)
    cB=(sb1-(1-cw))/(rt*sw); cT=(s1-(1-cw))/(rt*sw)
    print(f"{i:>3} {mp.nstr(cB,9):>26} {mp.nstr(cT,9):>28} {mp.nstr(cB-cT,6):>12} {mp.nstr(-1/mp.sqrt(2),7):>12}")
    sys.stdout.flush(); mp.mp.dps=60
print(" [Se=1-Sb1; at pole Sig1=1 => Se = Sig1-Sb1 = (cT-cB)rt sinw = -(cB-cT)rt sinw.]")
print(" [Need cB-cT = -1/sqrt2 so Se=(1/sqrt2)rt sinw, matching So.]")

print()
print("="*100)
print("CLOSURE CHECK 3 (R2): P12 in terms of blocks? Test P12 = -(p/(2q))*(Sig0 - Sb0)*(something)")
print("  and the clean asymptotic P12 ~ (1/(4sqrt2)) tau^{3/2} sin w.")
print("="*100)
print(f"{'m':>3} {'P12':>16} {'Sig0-Sb0':>15} {'(p/2q)(Sig0-Sb0)':>18} {'P12/[(p/2q)(Sig0-Sb0)]':>23}")
for i in [2,4,8,16,24]:
    q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q
    N=int(45/(1-q))
    P12,P22,_,_=cocycle(q,N)
    s0=Sig(0,q); sb0=Sb(0,q)
    d=s0-sb0
    cand=(p/(2*q))*d
    print(f"{i:>3} {mp.nstr(P12,9):>16} {mp.nstr(d,8):>15} {mp.nstr(cand,9):>18} {mp.nstr(P12/cand,9):>23}")
