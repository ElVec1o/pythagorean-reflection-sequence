"""
PART 7 (DECISIVE for V-footing vs named-fact): use the GENUINE lem:cos leading term for Se,
and find the genuine leading term for P12. Decide whether the tau/4 ratio needs the lem:cos VALUE
(saddle constant) or only its BOUND.

Facts to use:
  Se = cos W - T2  (EXACT, T1 cancels; lem:cos: T2 ~ (sqrt2/36) sqrt(tau) sinw, |T2|=O(sqrt tau)).
  So at a pole Se = cos W + O(sqrt tau).   cos W is ELEMENTARY (W=w e^{-tau/2}).
  S0b ~ w sin w  (PROVEN numerator thm).   S0b*Se -> sin^2 w = 1 (PART 2).
EXACT: t1 = D/(S0b Se), D = P12 S0b = 1 - P11 Se.   R2 <=> D -> tau/4.

QUESTION: write Se = cosW - T2 and P12 = ? Find the genuine P12 leading L_P so P12 = L_P - T2' with
T2'=O(?) lem:cos-class. Then t1 = P12/Se = (L_P - T2')/(cosW - T2). For t1->tau/4 from the BOUND alone
we need L_P/cosW -> tau/4 ELEMENTARY and T2',T2 = o(leading) by the BOUND. Test candidates for L_P:
   (i)  L_P = (1/2)(w-W)^2 cos W            [pure elementary, partner of cosW]
   (ii) L_P = (1/2)(w-W)^2 sinw sin(w-W)    [the CLAIM-A E]
Measure P12 - L_P for each; whichever gives a remainder = O(sqrt(tau)*leading)=O(tau^2) of lem:cos type wins.
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
print("PART 7 -- genuine leading terms. T2 := cosW - Se (the EXACT lem:cos remainder). orders via log-log slope.")
print("="*112)
print(f"{'m':>3} {'tau':>10} | {'T2=cosW-Se':>12} {'T2/sqtau':>9} | {'P12-Lp(i)':>12} {'/cosW/(tau/4)slack':>9} | {'P12-Lp(ii)':>12}")
taus=[];T2s=[];Ri=[];Rii=[]; LPi_ratio=[]
for m in [4,8,12,16,20,24,28,32]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=90+int(3.2*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(120/(1-q))
    W=w*mp.e**(-tau/2)
    P12,Se,P11,P21=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W); cosW=mp.cos(W)
    T2=cosW-Se
    Lp_i=mp.mpf(1)/2*(w-W)**2*cosW          # candidate (i): elementary partner of cosW
    Lp_ii=mp.mpf(1)/2*(w-W)**2*sw*swW        # candidate (ii): CLAIM-A E
    ri=P12-Lp_i; rii=P12-Lp_ii
    taus.append(float(tau)); T2s.append(abs(float(T2))); Ri.append(abs(float(ri))); Rii.append(abs(float(rii)))
    LPi_ratio.append(float((Lp_i/cosW)/(tau/4)))
    print(f"{m:>3} {float(tau):>10.3e} | {float(T2):>12.4e} {float(T2/mp.sqrt(tau)):>9.5f} | {float(ri):>12.4e} {float((Lp_i/cosW)/(tau/4)):>9.6f} | {float(rii):>12.4e}")
    mp.mp.dps=90
print()
print(f"  slope(|T2|) vs tau            = {slope(taus,T2s):.3f}   (lem:cos says T2~tau^0.5)")
print(f"  slope(|P12 - Lp(i)|) vs tau   = {slope(taus,Ri):.3f}   (need >1.5 for Lp(i) to be P12's leading)")
print(f"  slope(|P12 - Lp(ii)|) vs tau  = {slope(taus,Rii):.3f}  (CLAIM-A E remainder order)")
print(f"  Lp(i)/cosW /(tau/4) -> {LPi_ratio[-1]:.6f}  : if ->1, the ELEMENTARY ratio (1/2)(w-W)^2 / 1 with cosW partner gives tau/4.")
print()
print("INTERPRETATION:")
print("  - If P12 - Lp(i) = O(tau^2) [slope>=2] with Lp(i)=(1/2)(w-W)^2 cosW PURE ELEMENTARY, then")
print("    t1 = P12/Se = [Lp(i)+O(tau^2)]/[cosW - T2] = (1/2)(w-W)^2 * [1+O(tau^{3/2})]/[1 - T2/cosW].")
print("    T2/cosW = O(sqrt tau) by lem:cos BOUND. => t1 -> (1/2)(w-W)^2 -> tau/4 using only the lem:cos O() BOUND.")
print("    THAT is V's footing (no saddle constant of P12 needed; P12's leading is elementary cosW-partner).")
print("  - If instead the only good leading term is (ii) with a remainder needing a saddle const, it's named-fact.")
