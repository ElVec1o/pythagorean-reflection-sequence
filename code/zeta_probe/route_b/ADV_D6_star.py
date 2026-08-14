"""
Dissect (*) = 1/(w sinw R11) - cosW + cosw to see if it is ELEMENTARY (so [S2]
is the only non-elementary residual) or if it hides another lem:cos-class bound.

Pieces:
  A := 1/(w sinw R11)      (= 1/P11)   ~ sqrt(tau/2)/sin w + ...
  B := cos w - cos W       (elementary given w,W; W=w e^{-tau/2})
  (*) = A - cosW + cosw = A + (cosw - cosW) = A + B... wait sign:
        (*) = A - cosW + cosw = A + (cosw - cosW).
Let me also use the pole condition cos w = c0 sqrt(tau) sin w, c0=sqrt2/36.

Decompose:
   A = 1/P11.  1/P11 - sqrt(tau/2)/sin w =: dA  (the R11 correction). Is dA = O(tau^{3/2})?
   cos w - cos W : elementary. Its leading order?
   And the pole condition: cos w itself = O(sqrt tau).
We want to see exactly which sub-pieces are O(sqrt tau) (cancelling) vs which are the
genuine O(tau^{3/2}) residual, and whether any sub-piece is NON-elementary (saddle).
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
print("Dissect (*). c0=sqrt2/36. Test elementarity of each sub-piece (scaled by tau^{3/2}).")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'dA=(1/P11-sqt(t/2)/sw)/t1.5':>27} {'(cosw-cosW)/t1.5':>17} {'cosw/t0.5':>11}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(3.0*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    sw=mp.sin(w)
    dA = (1/P11 - mp.sqrt(tau/2)/sw)/tau**s32
    cwcW = (mp.cos(w)-mp.cos(W))/tau**s32
    cwh = mp.cos(w)/mp.sqrt(tau)
    print(f"{m:>3} {float(tau):>11.4e} {float(dA):>27.7f} {float(cwcW):>17.7f} {float(cwh):>11.7f}")
    mp.mp.dps=50

print("\nReconstruct (*)/t1.5 = [sqrt(t/2)/sw]/t1.5 + dA + (cosw - cosW)/t1.5")
print("  Note [sqrt(t/2)/sw]/t1.5 = 1/(sqrt2 sw tau).  This is O(1/tau) -> must cancel cosW.")
print("  Let me regroup honestly:  (*) = 1/P11 - cosW + cosw")
print("    = [1/P11] + [cosw - cosW].  1/P11=O(sqrt t), (cosw-cosW)=? ")
print(f"{'m':>3} {'tau':>11} {'(1/P11)/sqt(t)':>15} {'(cosw-cosW)/sqt(t)':>19} {'sum=(*)/sqt(t)':>15}")
for m in [8,16,32,50,70]:
    q0=poles[m-1]; tau0=-mp.log(q0); w0=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(3.0*float(w0)); q0=poles[m-1]
    q=refine_pole(q0); tau=-mp.log(q); w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); N=int(110/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    a=(1/P11)/mp.sqrt(tau)
    b=(mp.cos(w)-mp.cos(W))/mp.sqrt(tau)
    print(f"{m:>3} {float(tau):>11.4e} {float(a):>15.9f} {float(b):>19.9f} {float(a+b):>15.9f}")
    mp.mp.dps=50
