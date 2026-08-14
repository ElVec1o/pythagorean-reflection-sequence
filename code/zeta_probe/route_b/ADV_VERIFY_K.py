"""
ADVERSARIAL VERIFY of G2.D.4 candidate (Angle 2).
Question: does the candidate produce an EXPLICIT finite tau-uniform K with
   | f(tau) - (a1 tau + a2 tau^2) | <= K tau^3 ?
where f(tau) = Y3(1/q)/[(3/sqrt2) tau^{3/2} sin w] - 1 at travel poles.

We compute the TRUE remainder directly from the exact cocycle (Y3 via exact identity),
using the KNOWN rational a1=2269/1296, a2=507266513/251942400.
Test: is r3 := (f - a1 tau - a2 tau^2)/tau^3 bounded & stable as tau->0?
Also test r2 := (f - a1 tau)/tau^2  to confirm a2, and r4 with a3.
"""
import mpmath as mp

POLES=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

a1 = mp.mpf(2269)/1296
a2 = mp.mpf(507266513)/251942400
a3 = mp.mpf(2097873762713657)/1199951262720000

def setdps(tau):
    mp.mp.dps = 60 + int(3.0*float(mp.sqrt(2/tau)))

def cocycle(q,N):
    x=mp.mpf(0); y=mp.mpf(1); X=mp.mpf(1); Y=mp.mpf(0); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),
                 X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y   # P12, Se

print(f"{'m':>3} {'tau':>12} {'f':>14} {'r2=(f-a1t)/t^2':>16} {'r3=(f-a1t-a2t2)/t^3':>20} {'r4 (with a3)':>16}")
rows=[]
for m in [4,6,8,10,12,16,20,25]:
    if m>=len(POLES): continue
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    q=POLES[m]; tau=-mp.log(q)
    w=mp.sqrt(2/tau); sinw=mp.sin(w)
    N=int(130/(1-q))
    P12,Se=cocycle(q,N)
    # Y3(1/q) from exact identity: Y3(1)=(1-q^3)P12/(2q^3); Y3(1/q)=3 Y3(1)-(1-q^-3)Se
    Y3_1   = (1-q**3)*P12/(2*q**3)
    Y3_1oq = 3*Y3_1 - (1-q**(-3))*Se
    target = (3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    f = Y3_1oq/target - 1
    r2 = (f - a1*tau)/tau**2
    r3 = (f - a1*tau - a2*tau**2)/tau**3
    r4 = (f - a1*tau - a2*tau**2 - a3*tau**3)/tau**4
    rows.append((float(tau),f,r2,r3,r4))
    print(f"{m:>3} {float(tau):>12.5e} {mp.nstr(f,7):>14} {mp.nstr(r2,8):>16} {mp.nstr(r3,8):>20} {mp.nstr(r4,8):>16}")

print()
print("DIAGNOSTIC:")
print(" - r2 should -> a2 = %s = %.6f if a2 correct" % (mp.nstr(a2,8), float(a2)))
print(" - r3 should -> a3 = %s = %.6f if a3 correct" % (mp.nstr(a3,8), float(a3)))
print(" - r4 should -> a4 (some O(1) const) if a3 correct and series continues")
print()
print(" KEY: is r3 BOUNDED & STABLE as tau->0? If yes, an explicit finite K>=sup|r3| exists numerically.")
print("      But the CANDIDATE (Angle 2) explicitly states givesExplicitK=false and produces NO such K.")
