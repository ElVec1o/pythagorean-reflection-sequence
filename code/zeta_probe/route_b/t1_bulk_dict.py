import mpmath as mp
mp.mp.dps=50
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
def Sb(k,q,J=40000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=alpha(k+2*j,q)*prod; prod*=gamma(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-150) and j>80: break
    return tot

# t1=P12/Se. P12=Y (grading-1 cocycle, source col (1,0)). Try to express P12 as a Pochhammer
# series analogous to So/Se. We have So,Se as series. Reverse-engineer P12 series from the recursion.
# The grading-1 source emits q^{2n} (c1=2q^{2n}) instead of q^n (c0=2q^n) - one extra power per layer.
# Conjecture: P12 has a Pochhammer form with shifted exponent. Build candidate:
#   Po = sum_j (-2p)^j q^{j(j+2)+1} (1-q) ... ? Try matching P12 to assorted series.
# Simpler: numerically express t1 = (1/2)*So_shift/Se? Test t1 vs (1/2)(So with q->? ) -- skip, just
# determine the bulk-block form of t1 directly. We test: t1 =? (p/2)*S0^{(shift)}/(1-S1).
print("Hunt for bulk-block form of t1. Known: So/Se=(p/2q)S0/(1-S1). Test t1 candidates.")
print(f"{'q':>7} {'t1':>15} {'(p/2)S0/(1-S1)':>16} {'q*So/Se':>14} {'(p/2q)*S0b1/(1-S1)':>18}")
for qf in ['0.85','0.9','0.93','0.97','0.99']:
    q=mp.mpf(qf); N=int(150/(1-q)); p=1-q; J=int(200/(1-q))
    Se,So=SeSo(q,J); P12,_,_,_=cocycle(q,N)
    t1=P12/Se
    b1=Sb(1,q); b0=Sb(0,q)
    c1=(p/2)*b0/(1-b1)
    c2=q*So/Se
    print(f"{qf:>7} {mp.nstr(t1,9):>15} {mp.nstr(c1,9):>16} {mp.nstr(c2,9):>14}")

# t1 is genuinely a SECOND cocycle quantity. The Wronskian x*Y-X*y=-1 gives Y=(X*y-1)/x... need x,X.
# Let's just establish the cleanest fact: P12/Se = t1 and verify the exact recursion-derived
# alternative formula for t1 to see if it telescopes to bulk blocks.
# Actually report: is P12 itself a recognizable q-series? print its small-q expansion.
print()
mp.mp.dps=40
q=mp.mpf('0.001')  # tiny q: P12 ~ leading powers
# build series coefficients of P12 in q by symbolic-ish: evaluate at several tiny q and fit
import mpmath
qs=[mp.mpf('1e-3'),mp.mpf('2e-3'),mp.mpf('3e-3')]
for q in qs:
    P12,Se,_,_=cocycle(q,200)
    print(f" q={float(q):.0e}: P12={mp.nstr(P12,10)}  P12/q^2={mp.nstr(P12/q**2,8)}  P12/(2q^2)={mp.nstr(P12/(2*q**2),8)}")
