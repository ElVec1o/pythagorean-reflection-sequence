"""
Independent check of STEP E (relative-order budget) and STEP F (E-leading), plus the
R = P12 - E = O(tau^{5/2}) claim, with a careful look at numerical stability at deep poles.

STEP F algebra to re-derive from scratch:
  w-W = w(1-e^{-tau/2}).  w=sqrt(2/tau).
  1-e^{-tau/2} = tau/2 - tau^2/8 + ... = (tau/2)(1 - tau/4 + ...)
  w-W = sqrt(2/tau)*(tau/2)(1-tau/4+...) = sqrt(2/tau)*(tau/2)*(...)
      = sqrt(tau/2)*(1-tau/4+...).    [since sqrt(2/tau)*tau/2 = tau/(2)*sqrt(2/tau)=sqrt(2)*tau/(2 sqrt(tau))=sqrt(tau)/sqrt2=sqrt(tau/2)]
  (w-W)^2 = (tau/2)(1-tau/4)^2 = (tau/2)(1-tau/2+...)
  sin(w-W) = (w-W) - (w-W)^3/6 + ... = sqrt(tau/2)(1-tau/4) - (tau/2)^{1.5}/6+... = sqrt(tau/2)(1 - tau/4 - tau/12 + ...)
  E = (1/2)(w-W)^2 sinw sin(w-W)
    = (1/2)(tau/2)(1-tau/2) * sinw * sqrt(tau/2)(1-tau/4-tau/12)
    = (1/2)(tau/2)^{3/2} sinw (1-tau/2)(1-tau/3) + ...    [(-tau/4-tau/12=-tau/3)]
  (1/2)(tau/2)^{3/2} = (1/2) tau^{3/2}/2^{3/2} = tau^{3/2}/2^{5/2} = tau^{3/2}/(4 sqrt2).  CONFIRMED E_lead.
  Next relative factor: (1-tau/2)(1-tau/3) = 1 - 5tau/6 + ... so E = E_lead (1 - 5tau/6 + O(tau^2)).
  => E/E_lead -> 1 with slope -5/6 ~ -0.8333.  Check numerically.
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

# E/E_lead slope check
print("STEP F: E/E_lead = 1 + s*tau + ...  predicted s = -5/6 = %.6f" % (-5/6))
ms=[4,6,8,10,12,16,20,25,30]; taus=[]; eel=[]
for m in ms:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    E=mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    Elead=tau**mp.mpf('1.5')/(4*mp.sqrt(2))*sinw
    eel.append(E/Elead); taus.append(tau)
ce=polyfit(taus,eel,4)
print("  E/E_lead: c0=%s (->1), c1=%s (-> -5/6?)" % (mp.nstr(ce[0],10), mp.nstr(ce[1],8)))

# STEP E: R = P12 - E, check R/tau^{5/2} BOUNDED and extract its limit.
print("\nSTEP E: R=(P12-E)/tau^{5/2} should be bounded; and (Y3inv-Y3lead)/tau^{5/2} bounded.")
print(" m    tau        R/tau^{5/2}      (Y3-Y3lead)/tau^{5/2}    P12/tau^{1.5}")
Rvals=[]; Rtaus=[]
for m in [4,6,8,10,12,16,20,25,30,35,40]:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(115/(1-q)); Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    E=mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    Y3invq=3*((1-q**3)*Pk/(2*q**3))-(1-q**(-3))*Se
    Y3lead=(3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw
    R=(Pk-E)/tau**mp.mpf('2.5')
    Ry=(Y3invq-Y3lead)/tau**mp.mpf('2.5')
    Rvals.append(R); Rtaus.append(tau)
    print(" %2d  %.3e  %+.8f       %+.8f          %.8f"
          % (m, float(tau), float(R), float(Ry), float(abs(Pk)/tau**mp.mpf('1.5'))))
cr=polyfit(Rtaus[:9],Rvals[:9],3)
print("  R/tau^{5/2} LS-limit = %s  (this is the O(tau^{5/2}) coefficient; BOUNDED => R=O(tau^{5/2}))" % mp.nstr(cr[0],8))

# Stability at deep poles: compare cocycle Y3 vs closed-form-derived Y3 at m>33 with HIGH dps.
print("\nStability at deep poles (boost dps): does (P12-E)/tau^{5/2} stay bounded?")
for m in [33,40,50,60,70,79]:
    q=POLES[m]; tau=-mp.log(q)
    mp.mp.dps = 60 + int(4.0*float(mp.sqrt(2/tau)))   # extra precision
    N=int(130/(1-q)); Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    E=mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    R=(Pk-E)/tau**mp.mpf('2.5')
    print("  m=%2d tau=%.3e dps=%d  R/tau^{5/2}=%+.6f  P12/E=%.8f  |P12|/t^1.5=%.7f"
          % (m, float(tau), mp.mp.dps, float(R), float(Pk/E), float(abs(Pk)/tau**mp.mpf('1.5'))))
