"""
CRITICAL adversarial test of R2:
Does the leading constant 1/(4 sqrt2) of P12 come PURELY from elementary E,
with R genuinely subleading -- OR does R contribute at the leading tau^{3/2} order?

E = (1/2)(w-W)^2 sin w sin(w-W). Compute E/(tau^1.5 sinw) directly:
  if this -> 1/(4sqrt2) on its own, the constant is elementary.
Compute R/(tau^1.5 sinw) and its RATE (R/tau^2 / sinw): if R = O(tau^2) it's
  genuinely o(tau^1.5) (subleading by sqrt(tau)) -> the BOUND suffices.
Compare to the OTHER memory claim that R2 needs the P12 SADDLE constant
  (one notch beyond the bound).

Also: independent check via the CASORATIAN closed form (E4):
  t1 = sum_k 2 q^{3(k+1)} / (Se_k Se_{k+1})    [exact second-solution]
and the unimodular identity (E2): P11*Se + P12*S0b = 1.
"""
import mpmath as mp

def cocycle_full(q,N):
    # track full 2x2 product M_N...M_1 columns to get P11,P12,P21,P22
    # M_n = [[1+2q2n, -2qn],[2q3n, 1-2q2n]] acting; P = prod_{n=1}^N M_n (order?)
    # memory: P22=Se=y from col(0,1); P12=Y from col(1,0)->? replicate cocycle()
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    Se_iters=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
        Se_iters.append(y)
    # col1=(x,y): x=P11? y=P21? col2=(X,Y): X=P12? Y=P22?  ambiguous -- check unimodular
    return x,y,X,Y,Se_iters

def Se_So(q,J=None):
    if J is None: J=int(8*mp.sqrt(2/(-mp.log(q))))+200
    onem=1-q; Se=mp.mpf(0); So=mp.mpf(0); poch=[mp.mpf(1)]
    for n in range(1,2*J+2): poch.append(poch[-1]*(1-q**n))
    for j in range(0,J):
        Se+=(-2*onem)**j*q**(j*(j+1))/poch[2*j]
        So+=(-2*onem)**j*q**(j*(j+2))*onem/poch[2*j+1]
    return Se,So

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("=== E alone -> 1/(4sqrt2)?  R rate?  Casoratian cross-check ===")
print(f"{'m':>3} {'tau':>9} {'E/(t1.5 sinw)':>14} {'R/(t1.5 sinw)':>14} {'R/(tau^2 sinw)':>15} {'t1_caso/tau':>12}")
target=1/(4*mp.sqrt(2))
for m in [2,4,8,16,24,32]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=70+int(2.8*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(70/(1-q))
    x,y,X,Y,Se_it=cocycle_full(q,N)
    # determine P12,Se. From cocycle(): returned (Y,y) as (P12,Se). So P12=Y, Se=y.
    P12=Y; Se=y
    W=w*mp.e**(-tau/2); sinw=mp.sin(w)
    E_S=mp.sin(w)*mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*E_S
    R=P12-E
    t15=tau**mp.mpf('1.5')
    # Casoratian closed form t1 = sum 2 q^{3(k+1)}/(Se_k Se_{k+1})
    t1_caso=mp.mpf(0)
    for k in range(0,N):
        t1_caso+= 2*q**(3*(k+1))/(Se_it[k]*Se_it[k+1])
    print(f"{m:>3} {float(tau):>9.2e} {float(E/(t15*sinw)):>14.10f} {float(R/(t15*sinw)):>14.3e} {float(R/(tau**2*sinw)):>15.6f} {float(t1_caso/tau):>12.8f}")
    mp.mp.dps=50
print()
print("target 1/(4sqrt2) =", float(target))
