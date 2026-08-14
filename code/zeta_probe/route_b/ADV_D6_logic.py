"""
Is the reduction "[E3] + [S2]  =>  gate" actually valid?

[E3]: P12 = 1/P11 - Se.
Claim of D6: the O(sqrt tau) parts of 1/P11 and Se cancel via [S2], leaving O(tau^{3/2}).

To bound |P12| = |1/P11 - Se| <= C tau^{3/2} we need the O(sqrt tau) coefficients
of 1/P11 and Se to MATCH to relative O(tau). Let me decompose EXACTLY:

  Se      = cos W - T2_Se                          (def)
  1/P11   = 1/(w sin w R11)                         (def of R11)

So P12 = 1/(w sin w R11) - cos W + T2_Se.

[S2] as stated: cos w - T2_Se = O(tau^{3/2}), i.e. T2_Se = cos w + O(tau^{3/2}).
Substitute: P12 = 1/(w sin w R11) - cos W + cos w + O(tau^{3/2}).

So to get P12=O(tau^{3/2}) we ALSO need
   1/(w sin w R11) - cos W + cos w = O(tau^{3/2}).             (*)
Is (*) automatic (elementary), or is it an ADDITIONAL bound beyond [S2]?
Test (*) numerically. If (*) is O(tau^{3/2}) for free, then [S2] alone closes it.
If (*) is itself O(sqrt tau) and only the COMBINATION with [S2] cancels, then [S2]
as stated is NOT sufficient -- you need a joint statement.
"""
import mpmath as mp

def cocycle_full(q, N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        x,y,X,Y=x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n)
    return X,Y,x,y

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S

def refine_pole(q0, iters=8):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=Sig_t(q)-1; fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h)
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-8)): break
    return q

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
s32=mp.mpf('1.5')

print("="*100)
print("Decompose P12 = 1/(w sinw R11) - cosW + T2_Se, and test the auxiliary identity (*)")
print("(*) := 1/(w sinw R11) - cosW + cosw  =?= O(tau^{3/2})  [needed in ADDITION to [S2]]")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'[S2]:(cosw-T2Se)/t1.5':>22} {'(*)/t1.5':>13} {'P12/t1.5':>11} {'sum check':>11}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(3.0*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22
    R11=P11/(w*mp.sin(w))
    T2Se=mp.cos(W)-Se
    s2 = (mp.cos(w)-T2Se)/tau**s32
    star = (1/(w*mp.sin(w)*R11) - mp.cos(W) + mp.cos(w))/tau**s32
    p12r=P12/tau**s32
    # P12 = (*) - [ (cos w - T2_Se) ]  ... let's verify: P12 = 1/P11 - Se = 1/P11 - cosW + T2Se
    #  = [1/P11 - cosW + cosw] - [cosw - T2Se] = (*)_unscaled - (cosw - T2Se)
    chk = star - s2 - p12r
    print(f"{m:>3} {float(tau):>11.4e} {float(s2):>22.7f} {float(star):>13.7f} {float(p12r):>11.7f} {float(chk):>11.2e}")
    mp.mp.dps=50

print("\nINTERPRETATION:")
print(" If (*)/t^1.5 is BOUNDED (O(1)) then it is an O(tau^{3/2}) quantity = ANOTHER subleading bound,")
print(" so [S2] ALONE is NOT sufficient: the gate needs BOTH [S2] and (*), OR a single joint bound.")
print(" P12/t^1.5 = (*)/t^1.5 - [S2].  Both pieces O(1) => P12=O(tau^{3/2}) needs both bounded.")
