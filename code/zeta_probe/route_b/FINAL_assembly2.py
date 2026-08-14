"""
CORRECTED end-to-end assembly. The D1 closed form is for L(1/q) ALONE; the literal
identity Y3(1/q)=3x^3 L is FALSE at the pole (Y3/(3x^3 L)->0.3076, a resummation defect,
per D3's own caveat). The CORRECT closed form for Y3(1/q) at the poles is fact 9:

    Y3(1/q) = (36/35) * N0 * x^{3/2} * J_{3/2}(W/q) + O(tau^{5/2}),
    N0 = 3 * 2^{3/2} sqrt(pi) / (4 W^{3/2}),   x=1/q,   J_{3/2}(z)=sqrt(2/(pi z))(sin z/z - cos z).

We use THIS for Y3(1/q), Se = cosW - T2 with T2 the lem:T2abs leading term (sqrt2/36) sqrt(tau) sinw,
the exact pref, and the pole condition cos w = (sqrt2/36) sqrt(tau) sin w (D4) to read off the gate.

  P12_pred = pref * Y3_pred  -  (2/3) Se_pred.

Then we verify:
  (B) Y3_pred matches cocycle Y3(1/q) to O(tau^2) RELATIVE  (=> O(tau^{5/2}) absolute, since Y3~tau^{3/2}).
  (C) P12_pred matches cocycle P12 with (P12_pred-P12)/tau^{3/2} -> 0  (O(sqrt tau) cancels)
      and |P12_pred|/tau^{3/2} -> 1/(4 sqrt2).
"""
import mpmath as mp

def setdps(tau):
    mp.mp.dps = 55 + int(3.0*float(mp.sqrt(2/tau)))

def cocycle(q,N):
    x=mp.mpf(0); y=mp.mpf(1); X=mp.mpf(1); Y=mp.mpf(0); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),
                 X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y

def J32(z):
    return mp.sqrt(2/(mp.pi*z))*(mp.sin(z)/z - mp.cos(z))

def Y3_pred(q,tau):
    """fact 9 closed form."""
    x=1/q; w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2)
    N0=3*2**mp.mpf('1.5')*mp.sqrt(mp.pi)/(4*W**mp.mpf('1.5'))
    return (mp.mpf(36)/35)*N0*x**mp.mpf('1.5')*J32(W/q)

POLES=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

def polyfit(taus,vals,deg):
    n=len(taus); A=mp.matrix(n,deg+1); b=mp.matrix(n,1)
    for i in range(n):
        for j in range(deg+1): A[i,j]=taus[i]**j
        b[i]=vals[i]
    return mp.lu_solve(A.T*A, A.T*b)

print("="*100)
print("CHECK B' -- Y3(1/q) via fact-9 closed form vs cocycle. Relative error order.")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'Y3_coc':>15} {'Y3_pred':>15} {'relerr':>12} {'relerr/tau':>11} {'relerr/tau^2':>12}")
taus=[]; rel=[]
for m in [4,6,8,10,12,16,20,25,30]:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(115/(1-q)); P12,Se=cocycle(q,N)
    Y3c = 3*((1-q**3)*P12/(2*q**3)) - (1-q**(-3))*Se
    Y3p = Y3_pred(q,tau)
    r=(Y3p-Y3c)/Y3c
    taus.append(tau); rel.append(r)
    print(f"{m:>3} {float(tau):>11.4e} {mp.nstr(Y3c,8):>15} {mp.nstr(Y3p,8):>15} {mp.nstr(r,5):>12} {float(r/tau):>11.6f} {float(r/tau**2):>12.4f}")
c1=polyfit(taus,[r/tau for r,tau in zip(rel,taus)],2)[0]
print(f"\n  relerr/tau LS-limit = {mp.nstr(c1,8)}  (relerr = O(tau) => Y3_pred = Y3_coc(1+O(tau)).")
print("  fact 9 gives Y3 to O(tau) RELATIVE; the residual O(tau) is the 47/48-class next-order.)")

print("\n"+"="*100)
print("CHECK C' -- FULL closed-form P12 = pref*Y3_pred - (2/3)(cosW - T2), T2=(sqrt2/36)sqrt(tau)sinw.")
print("="*100)
print(f"{'m':>3} {'tau':>11} {'P12_coc':>15} {'P12_pred':>15} {'(pred-coc)/t^1.5':>17} {'|pred|/t^1.5':>12} {'|coc|/t^1.5':>12}")
taus3=[]; dd=[]; gp=[]
for m in [4,6,8,10,12,16,20,25,30]:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(115/(1-q)); P12,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    pref=2*q**3/(3*(1-q**3))
    Y3p=Y3_pred(q,tau)
    T2=(mp.sqrt(2)/36)*mp.sqrt(tau)*sinw
    Se_pred=mp.cos(W)-T2
    P12_pred=pref*Y3p-(mp.mpf(2)/3)*Se_pred
    d=(P12_pred-P12)/tau**mp.mpf('1.5')
    taus3.append(tau); dd.append(d); gp.append(abs(P12_pred)/tau**mp.mpf('1.5'))
    print(f"{m:>3} {float(tau):>11.4e} {mp.nstr(P12,8):>15} {mp.nstr(P12_pred,8):>15} {float(d):>17.9f} {float(abs(P12_pred)/tau**mp.mpf('1.5')):>12.7f} {float(abs(P12)/tau**mp.mpf('1.5')):>12.7f}")
cd=polyfit(taus3,dd,3)[0]
cg=polyfit(taus3,gp,3)[0]
print(f"\n  (P12_pred-P12)/tau^(3/2) LS-limit = {mp.nstr(cd,6)}  -> 0  => O(sqrt tau) terms CANCEL in assembly.")
print(f"  |P12_pred|/tau^(3/2) LS-limit = {mp.nstr(cg,8)}   target 1/(4 sqrt2) = {mp.nstr(1/(4*mp.sqrt(2)),8)}")
