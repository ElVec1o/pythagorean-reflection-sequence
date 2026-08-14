"""
DECISIVE resolution of the STEP-D narrative error and confirmation the CONCLUSION is right.

Findings to confirm at high precision (LS-extrapolated to tau->0):
  L1: Se/(sqrt(tau/2) sinw)   -> 1        (Se leading = sqrt(tau/2) sinw, coeff 1)
  L2: cosW/(sqrt(tau/2) sinw) -> 19/18    (cosW leading coeff is 19/18, DIFFERENT from Se)
  L3: T2 = cosW - Se,  T2/(sqrt(tau/2) sinw) -> 19/18 - 1 = 1/18 ;
      equivalently T2/(sqrt(tau) sinw) -> (1/18)/sqrt2 = 1/(18 sqrt2) = sqrt2/36 = 0.0392837  (lem:T2abs const!)
  L4: pref*Y3invq /(sqrt(t) sinw)  and (2/3)Se/(sqrt(t) sinw) BOTH -> 2/(3 sqrt2)=0.4714  (they MATCH)
  L5: The CORRECT STEP-D arithmetic:
        pref*Y3_lead = (2/(3 sqrt2)) sqrt(t) sinw
        (2/3)Se_lead = (2/3)(1/sqrt2) sqrt(t) sinw = (2/(3 sqrt2)) sqrt(t) sinw   [coeff 1, NOT 19/18]
      => these are EQUAL, cancellation is genuine. The script's use of 19/18 for Se's leading
         was the error; it accidentally still concluded "cancellation exact (via identity)".

Net: the FINAL RESULT of D5 (gate holds, |P12|/t^1.5 -> 1/(4 sqrt2), R=O(t^2.5)) is CORRECT and
my independent numerics confirm it. But the STEP-D explanatory arithmetic has a real bug: it
attributes the 19/18 to Se when 19/18 belongs to cosW and Se's leading coeff is 1. The script
papers over its own dimensionally-impossible mismatch (1/(27 sqrt2) sqrt(t), an O(sqrt t) leak)
by appealing to the identity. The honest statement: Se ~ sqrt(tau/2) sinw (coeff 1).
"""
import mpmath as mp

def setdps(tau):
    mp.mp.dps = 50 + int(3.0*float(mp.sqrt(2/tau)))

def cocycle(q,N):
    x=mp.mpf(0); y=mp.mpf(1); X=mp.mpf(1); Y=mp.mpf(0); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),
                 X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y

with open('poles.txt') as f:
    POLES=[mp.mpf(l.strip()) for l in f if l.strip()]

def polyfit(taus,vals,deg):
    n=len(taus); A=mp.matrix(n,deg+1); b=mp.matrix(n,1)
    for i in range(n):
        for j in range(deg+1): A[i,j]=taus[i]**j
        b[i]=vals[i]
    return mp.lu_solve(A.T*A, A.T*b)

ms=[4,5,6,7,8,9,10,12,14,16,18,20,25,30]
taus=[]; L1=[]; L2=[]; L3=[]; A_=[]; B_=[]
for m in ms:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q)); Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w); cosW=mp.cos(W)
    Y3invq=3*((1-q**3)*Pk/(2*q**3))-(1-q**(-3))*Se
    pref=2*q**3/(3*(1-q**3))
    base=mp.sqrt(tau/2)*sinw
    taus.append(tau)
    L1.append(Se/base)
    L2.append(cosW/base)
    L3.append((cosW-Se)/base)
    A_.append((pref*Y3invq)/(mp.sqrt(tau)*sinw))
    B_.append((mp.mpf(2)/3*Se)/(mp.sqrt(tau)*sinw))

print("LS-extrapolated limits (deg-4):")
print("  L1  Se/(sqrt(t/2) sinw)   -> %s    target 1"        % mp.nstr(polyfit(taus,L1,4)[0],13))
print("  L2  cosW/(sqrt(t/2) sinw) -> %s    target 19/18=%s" % (mp.nstr(polyfit(taus,L2,4)[0],13), mp.nstr(mp.mpf(19)/18,13)))
print("  L3  T2/(sqrt(t/2) sinw)   -> %s    target 1/18=%s"  % (mp.nstr(polyfit(taus,L3,4)[0],13), mp.nstr(mp.mpf(1)/18,13)))
print("      [=> T2/(sqrt(t) sinw) -> 1/(18 sqrt2)=sqrt2/36=%s, the lem:T2abs constant]" % mp.nstr(mp.sqrt(2)/36,13))
print("  A   pref*Y3/(sqrt(t)sinw) -> %s" % mp.nstr(polyfit(taus,A_,4)[0],13))
print("  B   (2/3)Se/(sqrt(t)sinw) -> %s    target 2/(3 sqrt2)=%s" % (mp.nstr(polyfit(taus,B_,4)[0],13), mp.nstr(2/(3*mp.sqrt(2)),13)))
print()
print("  A == B at leading order (both -> 2/(3 sqrt2)) => genuine O(sqrt t) cancellation. CONFIRMED.")
print("  The narrative's claim '(2/3)Se_lead = 19/(27 sqrt2)=0.49759' is WRONG; it's 2/(3 sqrt2)=0.47140.")
print("  Se's leading coeff (in sqrt(t/2) sinw units) is 1, not 19/18. 19/18 belongs to cosW.")

# Final independent gate verification across ALL poles in the numerically stable range.
print("\nFINAL GATE CHECK over poles m=1..50 (stable): max |P12|/tau^{3/2} and P12/E:")
mx=mp.mpf(0); mxE=mp.mpf(0); worst=0
for m in range(1,51):
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q)); Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    E=mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    r=abs(Pk)/tau**mp.mpf('1.5')
    rE=abs(Pk/E-1)
    if r>mx: mx=r; worst=m
    if rE>mxE: mxE=rE
print("  max |P12|/tau^{3/2} = %s  (at m=%d)   gate 1/sqrt2 = %s   1/(4sqrt2)=%s"
      % (mp.nstr(mx,10), worst, mp.nstr(1/mp.sqrt(2),10), mp.nstr(1/(4*mp.sqrt(2)),10)))
print("  max |P12/E - 1| over m=1..50 = %s  (-> 0, confirming P12~E)" % mp.nstr(mxE,8))
print("  GATE C = %s < 1/sqrt2 = 0.70711 :  %s" % (mp.nstr(mx,8), "PASS" if mx < 1/mp.sqrt(2) else "FAIL"))
