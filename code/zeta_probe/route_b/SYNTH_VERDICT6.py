"""
PART 9 (final adversarial): is the P12 remainder Rho CONTROLLED BY the same lem:cos object T2,
or is it an INDEPENDENT estimate (=> named fact)?

We have EXACT: t1 = P12/Se.  Define the lem:cos remainder T2 = cosW - Se (order tau^{1/2}, |T2|=O(sqrt tau) is lem:Bbounded).
Test the IDENTITY-level relation between P12 and Se's pieces. P12 and Se solve the SAME recursion
  y_{n+1} = (1+q^3 - 2(1-q)q^{2n+2}) y_n - q^3 y_{n-1}   (memory E0).
Se=P22: (y0,y1)=(1,1-2q^2).  P12: (y0,y1)=(0,2q^3).  So P12 is the 2nd solution.
There is an EXACT Casoratian C_n = P12_{n+1} Se_n - P12_n Se_{n+1} = 2 q^{3(n+1)} (memory E4) =>
  t1 = P12_inf/Se_inf = sum_{n>=0} 2 q^{3(n+1)}/(Se_n Se_{n+1})   (telescoping VOP; EXACT).

The cleanest honest question for the verdict: can I get  |t1 - (1/2)(w-W)^2| -> 0  using ONLY
(a) the lem:cos BOUND |T2|=|cosW-Se|=O(sqrt tau)  [=> Se = cosW + O(sqrt tau), and Se bounded below ~ sqrt(tau/2)], and
(b) an analogous BOUND on the SINE-partner P12, namely |P12 - (1/2)(w-W)^2 cosW| = O(tau^2)?
If (b) is the SAME steepest-descent object as (a) (same B_s, same contour), it's V-footing. Test (b)'s order:
"""
import mpmath as mp

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
import math
def slope(xs,ys):
    lx=[math.log(x) for x in xs]; ly=[math.log(abs(y)) for y in ys]
    n=len(lx); sx=sum(lx); sy=sum(ly); sxx=sum(t*t for t in lx); sxy=sum(lx[i]*ly[i] for i in range(n))
    return (n*sxy-sx*sy)/(n*sxx-sx*sx)

print("="*112)
print("PART 9 -- decompose using cosW (the genuine lem:cos leading): P12 = (1/2)(w-W)^2 cosW - Tp,  Se = cosW - T2.")
print("  Then t1 = P12/Se = [(1/2)(w-W)^2 cosW - Tp]/[cosW - T2].  Want: Tp, T2 both o(leading) by BOUND.")
print("  Tp := (1/2)(w-W)^2 cosW - P12.  Compare Tp to (1/2)(w-W)^2 * T2  (the 'expected' if P12 ~ (1/2)(w-W)^2 Se).")
print("="*112)
print(f"{'m':>3} {'tau':>10} | {'T2=cosW-Se':>12} {'Tp':>12} {'(1/2)(w-W)^2*T2':>15} {'Tp/[(..)T2]':>11} | {'t1':>12} {'predict':>12}")
taus=[];Tps=[]
for m in [4,8,12,16,20,24,28,32]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=90+int(3.2*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(120/(1-q))
    W=w*mp.e**(-tau/2)
    P12,Se,P11,P21=cocycle(q,N)
    cosW=mp.cos(W); half=mp.mpf(1)/2*(w-W)**2
    T2=cosW-Se
    Tp=half*cosW-P12
    expected=half*T2
    # prediction: t1 = (half*cosW - Tp)/(cosW - T2). If Tp = half*T2 EXACTLY then t1=half EXACTLY.
    pred=(half*cosW-Tp)/(cosW-T2)
    taus.append(float(tau)); Tps.append(abs(float(Tp-expected)))
    print(f"{m:>3} {float(tau):>10.3e} | {float(T2):>12.4e} {float(Tp):>12.4e} {float(expected):>15.4e} {float(Tp/expected):>11.7f} | {float(P12/Se):>12.8f} {float(pred):>12.8f}")
    mp.mp.dps=90
print()
print(f"  slope(|Tp - (1/2)(w-W)^2 T2|) vs tau = {slope(taus,Tps):.3f}")
print()
print("KEY READING:")
print("  Tp/[(1/2)(w-W)^2 T2] -> 1  would mean  Tp = (1/2)(w-W)^2 T2 + o(...), i.e. the sine-partner's")
print("  deviation from (1/2)(w-W)^2 cosW is EXACTLY (1/2)(w-W)^2 times the SAME lem:cos remainder T2,")
print("  plus a higher-order piece. Then  t1 = (half cosW - half T2 - rest)/(cosW - T2)")
print("       = (half(cosW - T2) - rest)/(cosW-T2) = half - rest/Se,  rest=Tp-half*T2 = o(tau^2).")
print("  => t1 = (1/2)(w-W)^2 - [o(tau^2)]/Se, and the WHOLE lem:cos dependence (T2) CANCELS in the ratio.")
print("  That is the strongest V-footing statement: the leading is elementary AND the lem:cos remainder cancels;")
print("  only a SUBLEADING bound rest=o(tau^2) (=> rest/Se=o(tau^{3/2})->0) remains, of lem:cos BOUND character.")
