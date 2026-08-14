"""
Are (*) and [S2] the SAME saddle bound, or two parallel ones?

(*)  = 1/P11 - cosW + cosw        [P11-side; non-elem part = R11 correction]
[S2] = cosw - T2_Se = cosw - cosW + Se   [Se-side; non-elem part = T2_Se]

The det identity at the pole is P11 Se + P12 P11 = 1 (i.e. P11(Se+P12)=1) which is
how E3 arose -- this is ONE scalar relation linking P11 and Se. Does it force the
P11-saddle to equal the Se-saddle (so (*) and [S2] are not independent)?

Test: define the two 'saddle defects'
   d_P11 := R11 - 1   (P11/(w sinw) - 1)     ~ -0.1242 tau
   d_Se  := Se/(sqrt(tau/2) sin w) - 1        ~ ? tau    (the Se cofactor defect)
Are they EQUAL? proportional? Their relation determines whether one bound suffices.

Also directly: is (*) = f(tau)*[S2] + elementary, for some clean f?
Compute (*)/[S2] and (*)-[S2] (=P12) and check.
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
s32=mp.mpf('1.5'); half=mp.mpf('0.5')

print("="*100)
print("Saddle defects of P11 and Se, and relation between (*) and [S2]")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'d_P11/tau':>12} {'d_Se/tau':>12} {'(*)/[S2]':>11} {'(*)+[S2]?':>11}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(3.0*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N); Se=P22; sw=mp.sin(w)
    d_P11 = P11/(w*sw) - 1
    d_Se  = Se/(mp.sqrt(tau/2)*sw) - 1
    star = 1/P11 - mp.cos(W) + mp.cos(w)
    s2u  = mp.cos(w) - (mp.cos(W)-Se)   # = cosw - T2_Se
    print(f"{m:>3} {float(tau):>11.4e} {float(d_P11/tau):>12.7f} {float(d_Se/tau):>12.7f} {float(star/s2u):>11.7f} {mp.nstr((star+s2u)/tau**s32,6):>11}")
    mp.mp.dps=50

print("\n  d_P11/tau -> ? ; d_Se/tau -> ?  (if EQUAL, P11 and Se share the SAME saddle defect)")
print("  (*)/[S2] -> ?  (if a clean constant, the two bounds are PROPORTIONAL = effectively one)")
print(f"  recall 1/(4 sqrt2)={float(1/(4*mp.sqrt(2))):.7f}; (*)-[S2]=P12 by construction.")
