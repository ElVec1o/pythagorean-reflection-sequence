"""
DECISIVE adversarial test of "R2 closes on V's footing".
Memory claim: t1 = P12/Se = (E+R)/(E_S+R_S) = (E/E_S)*(1+R/E)/(1+R_S/E_S),
  E/E_S = (1/2)(w-W)^2 EXACT ELEMENTARY -> tau/4,
  R/E = o(1) and R_S/E_S = o(1) by lem:cos BOUND ONLY.
Need: (i) E/E_S exactly (1/2)(w-W)^2 (algebraic, no saddle). (ii) R/E -> 0. (iii) R_S/E_S -> 0.
If (ii)+(iii) hold with the SAME character as R1 (controlled by O(sqrt tau)/O(tau) BOUND, not a
saddle CONSTANT), then R2 closes on V's footing.

ADVERSARIAL POINTS TO WATCH:
 - Is R_S/E_S genuinely o(1)?  Se=E_S+R_S; R_S is the lem:cos T2 piece (~sqrt(tau)) and E_S~sqrt(tau);
   so R_S/E_S = O(1) RATIO of two sqrt(tau) things -- does it actually -> 0, or to a CONSTANT?
   If R_S/E_S -> nonzero const, then E/E_S alone is NOT the full t1 leading ratio and the lem:cos
   SADDLE CONSTANT (not just bound) is needed -- exactly the prompt-summary's claim. CHECK THIS.
"""
import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y   # P12, P22=Se
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
print(f"{'m':>3} {'tau':>9} {'Se/sqrt(tau/2)':>13} {'E_S/sqrt(t/2)':>13} {'R_S/E_S':>10} {'R/E':>10} {'(E/E_S)/(tau/4)':>14} {'t1/tau':>9}")
for m in [1,2,4,8,16,24,32,40,48]:
    if m>len(poles): continue
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=55+int(2.2*float(w))
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); p=1-q; N=int(70/p)
    W=w*mp.e**(-tau/2)
    P12,Se=cocycle(q,N)
    sw=mp.sin(w); swW=mp.sin(w-W)
    ES=sw*swW
    E=mp.mpf(1)/2*(w-W)**2*ES
    RS=Se-ES; R=P12-E
    EoverES=E/ES   # = (1/2)(w-W)^2 by construction
    t1=P12/Se
    sqth=mp.sqrt(tau/2)
    print(f"{m:>3} {float(tau):>9.2e} {float(Se/sqth):>13.7f} {float(ES/sqth):>13.7f} {float(RS/ES):>10.3e} {float(R/E):>10.3e} {float(EoverES/(tau/4)):>14.9f} {float(t1/tau):>9.6f}",flush=True)
    mp.mp.dps=40
