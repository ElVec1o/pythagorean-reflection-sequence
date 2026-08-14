"""
The load-bearing question: WHAT must be granted for t1/tau->1/4?

t1 = P12/Se. Write Se = E_S + R_S, P12 = E + R with
  E_S = sinw sin(w-W),  E = (1/2)(w-W)^2 E_S.
Then t1 = (E/E_S) * (1+R/E)/(1+R_S/E_S) = (1/2)(w-W)^2 * (1+R/E)/(1+R_S/E_S).

The factor (1/2)(w-W)^2 -> tau/4 is ELEMENTARY (only tau). So
  t1/tau -> 1/4   <=>   R/E -> 0  AND  R_S/E_S -> 0.

Q1: Is "R_S/E_S -> 0" the SAME statement as lem:cos (Se ~ E_S), or weaker/stronger?
    lem:cos (extreme-phase form) gives Se = E_S + O(tau) with E_S ~ sqrt(tau/2) sinw,
    so R_S/E_S = O(tau)/O(sqrt tau)=O(sqrt tau)->0.  => R_S/E_S->0 is IMPLIED by the
    lem:cos BOUND. (NOT its saddle value.) Verify numerically R_S/E_S ~ C*sqrt(tau) or smaller.
Q2: Is "R/E -> 0" implied by a bound of the SAME class (lem:Bbounded on the P12 cocycle
    partner), or does it need the P12 SADDLE VALUE?
    R/E -> 0 only needs R = o(E) = o(tau^{3/2} sinw). The memory's *other* claim was that
    one needs P12 ~ tau^{3/2}/(4sqrt2) sinw -- i.e. the VALUE. But that VALUE = E's value!
    So if R=o(E) (a bound), the value is automatically supplied by E (elementary).
    => Check: is R=o(E) provable as a bound, or is R itself ~ c*E (a constant fraction,
    which would mean the elementary E is NOT the whole leading term)?
    Test: R/E -> 0 strictly (already saw ~tau). Fit R/E ~ C tau^p.
"""
import mpmath as mp

def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

rows=[]
for m in [4,8,16,24,32,40]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=70+int(2.8*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    N=int(70/(1-q))
    P12,Se=cocycle(q,N)
    W=w*mp.e**(-tau/2); sinw=mp.sin(w)
    E_S=mp.sin(w)*mp.sin(w-W)
    E=mp.mpf(1)/2*(w-W)**2*E_S
    R_S=Se-E_S; R=P12-E
    rows.append((m,tau,R/E,R_S/E_S))
    mp.mp.dps=50

print(f"{'m':>3} {'tau':>9} {'R/E':>12} {'(R/E)/tau':>10} {'R_S/E_S':>12} {'(R_S/E_S)/sqrt(t)':>16}")
for (m,tau,re,rse) in rows:
    print(f"{m:>3} {float(tau):>9.2e} {float(re):>12.4e} {float(re/tau):>10.5f} {float(rse):>12.4e} {float(rse/mp.sqrt(tau)):>16.6f}")

# fit exponents
import math
def fitp(xs):
    # xs = list of (tau, val) ; fit |val| ~ C tau^p via two endpoints
    (t1,v1),(t2,v2)=xs[0],xs[-1]
    p=math.log(abs(v2)/abs(v1))/math.log(float(t2)/float(t1))
    return p
re_pts=[(t,re) for (m,t,re,rse) in rows]
rse_pts=[(t,rse) for (m,t,re,rse) in rows]
print()
print(f"R/E      ~ tau^{fitp(re_pts):.3f}   (need >0 => R/E->0, a BOUND suffices)")
print(f"R_S/E_S  ~ tau^{fitp(rse_pts):.3f}   (need >0 => R_S/E_S->0, lem:cos BOUND suffices)")
