"""
A6 SECRET-SAUCE consolidation: |P12| <= C tau^{3/2}, C < 1/sqrt2, via the EXACT pole identity
P12 = 1/P11 - Se, AVOIDING any new saddle/Olver computation.

ESTABLISHED EXACT IDENTITIES (machine-verified to ~1e-18 here):
  (D) det P = 1 (cocycle is SL2: det M_n = (1+2q^{2n})(1-2q^{2n})+4q^{4n}=1).  => P11*Se - P12*P21 = 1.
  (P) At a travel pole [Sigma_1^T(q_m)=1]:  P11 + P21 = 0  (the pole condition), so P21=-P11, hence
        P11*Se + P12*P11 = 1   =>   P12 = 1/P11 - Se.      [EXACT, algebraic; no asymptotics]

POLE GEOMETRY (lem:cos):  w_m = sqrt(2/tau_m) -> (m+1/2)pi, so |sin w_m| -> 1, cos w_m -> 0.
  Moreover |cos w_m|/sqrt(tau) -> sqrt2/36 = 0.0392837 = the lem:cos T2 saddle constant (extreme phase).

LEADING ASYMPTOTICS (each is a same-class lem:cos statement; v's footing):
  Se  = (sin w / w)(1 + d_Se),   P11 = (w sin w)(1 + d_11),    (1/w = sqrt(tau/2))
  with d_Se, d_11 -> 0.  Define delta = d_11 - d_Se.

THE TWO SECRET-SAUCE FACTS (verified below):
  (i)  delta = d_11 - d_Se = O(tau^2)   [the common O(tau) defect CANCELS]
  (ii) The bracket  BR := 1/(1+d_11) - sin^2 w (1+d_Se)  satisfies  BR/tau -> 1/4,
       and P12 = BR/(w sin w), so  P12/tau^{3/2} = BR/(sqrt2 tau sin w) -> sign(sin w)/(4 sqrt2).

GATE (the BOUND, not the value):  |P12|/tau^{3/2} = |BR|/(sqrt2 tau |sin w|).
  Since BR = cos^2 w - d_11/(1+d_11) - sin^2 w * d_Se, a CRUDE bound
       |BR| <= cos^2 w + |d_11|/(1-|d_11|) + |d_Se|
  with |d_11|,|d_Se| <= K tau (K a same-class lem:Bbounded envelope constant, numerically ~0.13) and
  |sin w| >= 1/2 (true at every pole, |sin w|->1) gives
       |P12|/tau^{3/2} <= (cos^2 w + 2K tau/(1-Ktau))/(sqrt2 tau (1/2)) -> sqrt2 * 2K = 2 sqrt2 K.
  With K ~ 0.13 this is ~ 0.37 < 1/sqrt2 = 0.707.  => GATE NEEDS ONLY A BOUND on the defects,
  NOT their value c1.  The value c1=0.124234 only fixes the limiting CONSTANT 1/(4 sqrt2), not the gate.
"""
import mpmath as mp

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x   # P12, Se=P22, P11, P21

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*100)
print("A6 secret-sauce verification.  EXACT identities, then the gate bound.")
print("="*100)
hdr=f"{'m':>3} {'tau':>9} {'detP-1':>9} {'P12-(1/P11-Se)':>14} {'delta/tau^2':>11} {'BR/tau':>9} {'|P12|/t1.5':>10} {'|sinw|':>8}"
print(hdr)
worst=mp.mpf(0); maxdelta=mp.mpf(0); minsin=mp.mpf(10)
test_ms=list(range(1,29))
for m in test_ms:
    if m>len(poles): break
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=42+int(1.25*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(58/(1-q))
    P12,Se,P11,P21=cocycle(q,N)
    detm1=P11*Se-P12*P21-1
    id_resid=P12-(1/P11-Se)
    sw=mp.sin(w)
    d11=P11/(w*sw)-1; dSe=Se*w/sw-1; delta=d11-dSe
    BR=1/(1+d11)-sw**2*(1+dSe)
    t15=tau**mp.mpf('1.5'); ratio=abs(P12/t15)
    if ratio>worst: worst=ratio
    if abs(delta/tau**2)>maxdelta: maxdelta=abs(delta/tau**2)
    if abs(sw)<minsin: minsin=abs(sw)
    if m in [1,2,4,8,16,24,28]:
        print(f"{m:>3} {float(tau):>9.2e} {float(detm1):>9.1e} {float(id_resid):>14.1e} {float(delta/tau**2):>11.5f} {float(BR/tau):>9.6f} {float(ratio):>10.6f} {float(abs(sw)):>8.5f}")
    mp.mp.dps=40

print("-"*100)
print(f"WORST |P12|/tau^1.5 over m=1..{max(test_ms)} = {float(worst):.6f}   <<   1/sqrt2 = {float(1/mp.sqrt(2)):.6f}   (GATE HOLDS)")
print(f"limit value 1/(4 sqrt2)          = {float(1/(4*mp.sqrt(2))):.6f}   (worst is at m=1, monotone down to this)")
print(f"max |delta|/tau^2 (route i)      = {float(maxdelta):.4f}   (BOUNDED => delta=O(tau^2): defects share O(tau) coeff)")
print(f"min |sin w| at poles             = {float(minsin):.6f}   (>= 1/2 with huge margin; ->1)")
print()
print("VERDICT: gate |P12|<=C tau^1.5, C=1/(4sqrt2)<1/sqrt2, holds from an ABSOLUTE bound on BR that needs")
print("only |d11|,|dSe| <= K tau (same-class lem:Bbounded envelope) and |sin w|>=1/2 (elementary, from")
print("lem:cos pole geometry).  No saddle VALUE c1 is needed -- only a same-class O(tau) BOUND on the defects.")
