"""
Richardson / least-squares extraction of the limit constants, and an ALGEBRAIC
cross-check of the STEP-D cancellation logic.

The key adversarial questions:
 1. Does Y3(1/q)/(tau^{3/2} sin w) -> 3/sqrt2 to many digits (not just 7)?
 2. Does the STEP-D *narrative* arithmetic hold up? It claims:
       pref*Y3_lead = (2/(3 sqrt2)) sqrt(tau) sin w
       (2/3) cos W  = (19/(27 sqrt2)) sqrt(tau) sin w
    and the difference (1/(27 sqrt2)) sqrt(tau) sin w is supposed to be E (= O(tau^{3/2}))???
    BUT (1/(27 sqrt2)) sqrt(tau) sin w is O(sqrt(tau)), NOT O(tau^{3/2}). Check this discrepancy.
 3. Independent check: is P12 = pref*Y3(1/q) - (2/3) Se really an O(tau^{3/2}) difference of two
    O(sqrt tau) quantities, i.e. genuine cancellation?
 4. Extract a1 (the next-order relative coeff of Y3(1/q)).
"""
import mpmath as mp

def setdps(tau):
    mp.mp.dps = 50 + int(3.0*float(mp.sqrt(2/tau)))

def cocycle(q, N):
    x=mp.mpf(0); y=mp.mpf(1); X=mp.mpf(1); Y=mp.mpf(0); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        x,y,X,Y = (x*(1+2*q2n)-2*y*qn, 2*x*q3n+y*(1-2*q2n),
                   X*(1+2*q2n)-2*Y*qn, 2*X*q3n+Y*(1-2*q2n))
    return Y,y

with open('poles.txt') as f:
    POLES=[mp.mpf(l.strip()) for l in f if l.strip()]

# ---------------------------------------------------------------
# Q1+Q4: fit ratio_Y3 = Y3inv/(tau^{3/2} sinw) = c0 + c1 tau + c2 tau^2 + ...
# Use a stable mid-range set of poles, polyfit in tau.
# ---------------------------------------------------------------
ms = [4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,25,28,30]
taus=[]; rats=[]; ratsCos=[]; ratsFact9=[]; ratsE=[]
for m in ms:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q))
    Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w); cosW=mp.cos(W)
    Y3invq = 3*((1-q**3)*Pk/(2*q**3)) - (1-q**(-3))*Se
    rats.append(Y3invq/(tau**mp.mpf('1.5')*sinw))
    ratsCos.append(cosW/(mp.sqrt(tau/2)*sinw))
    N0=3*2**mp.mpf('1.5')*mp.sqrt(mp.pi)/(4*W**mp.mpf('1.5'))
    ratsFact9.append(Y3invq/(N0*(1/q)**mp.mpf('1.5')*mp.besselj(mp.mpf(3)/2,W/q)))
    E=mp.mpf(1)/2*(w-W)**2*sinw*mp.sin(w-W)
    ratsE.append(Pk/E)
    taus.append(tau)

def polyfit_const(taus, vals, deg):
    # least squares fit vals ~ sum_j c_j tau^j ; return c0 (the limit)
    n=len(taus)
    A=mp.matrix(n, deg+1)
    b=mp.matrix(n,1)
    for i in range(n):
        for j in range(deg+1):
            A[i,j]=taus[i]**j
        b[i]=vals[i]
    # normal equations
    AT=A.T
    c=mp.lu_solve(AT*A, AT*b)
    return c

print("Richardson/LS fits (deg=4) of limit constants:")
for name, vals, target in [
    ("Y3inv/(t^1.5 sinw)", rats, 3/mp.sqrt(2)),
    ("cosW/(sqrt(t/2)sinw)", ratsCos, mp.mpf(19)/18),
    ("fact9 ratio", ratsFact9, mp.mpf(36)/35),
    ("P12/E", ratsE, mp.mpf(1)),
]:
    c=polyfit_const(taus, vals, 4)
    print("  %-22s c0=%s  target=%s  c1=%s"
          % (name, mp.nstr(c[0],14), mp.nstr(target,14), mp.nstr(c[1],8)))

# ---------------------------------------------------------------
# Q2: examine the STEP-D narrative arithmetic dimension by dimension.
# pref*Y3invq and (2/3)Se are each O(sqrt tau). Their leading sqrt(tau) coeffs:
#   A := (pref*Y3invq)/(sqrt(tau) sinw),  B := ((2/3)Se)/(sqrt(tau) sinw)
# The script narrative says A_lead = 2/(3 sqrt2) = 0.4714, B_lead = 19/(27 sqrt2)=0.4976.
# Their difference should be P12/(sqrt(tau) sinw) -> ??? If P12=O(tau^{3/2}) then this -> 0.
# So A_lead and B_lead MUST be EQUAL in the limit. Check whether 2/(3 sqrt2) == 19/(27 sqrt2).
# 2/(3 sqrt2) = 18/(27 sqrt2). NOT equal to 19/(27 sqrt2). So the NARRATIVE is internally wrong
# UNLESS Y3_lead is actually (19/18)*(3/sqrt2)=19/(6 sqrt2), not 3/sqrt2 (and the 3/sqrt2 is only
# the sin-w coefficient that does NOT itself cancel cosW -- the cosW carries 19/18). Investigate.
# ---------------------------------------------------------------
print("\nQ2: leading sqrt(tau) coefficients of pref*Y3 and (2/3)Se (must MATCH for cancellation):")
print(" m    A=(pref Y3)/(sqrt t sinw)   B=((2/3)Se)/(sqrt t sinw)   A-B (= P12/(sqrt t sinw) ->0?)")
for m in [3,6,12,25,40,60]:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q))
    Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    Y3invq = 3*((1-q**3)*Pk/(2*q**3)) - (1-q**(-3))*Se
    pref=2*q**3/(3*(1-q**3))
    A=(pref*Y3invq)/(mp.sqrt(tau)*sinw)
    B=(mp.mpf(2)/3*Se)/(mp.sqrt(tau)*sinw)
    print(" %2d   %.10f               %.10f               %+.4e"
          % (m, float(A), float(B), float(A-B)))
print("  narrative claims A_lead=2/(3 sqrt2)=%.8f, B_lead=19/(27 sqrt2)=%.8f (these DIFFER!)"
      % (float(2/(3*mp.sqrt(2))), float(19/(27*mp.sqrt(2)))))
print("  TRUE common limit should be: pref*Y3_lead = (2/(9tau))(3/sqrt2 t^1.5 sinw)= (2/(3sqrt2)) sqrt t sinw = %.8f"
      % float(2/(3*mp.sqrt(2))))
print("  and (2/3)*(19/18) sqrt(t/2) sinw = (2/3)(19/18)(1/sqrt2) sqrt t sinw = %.8f"
      % float(2*19/(3*18*mp.sqrt(2))))

# ---------------------------------------------------------------
# Q3: extract a1 from Y3inv = (3/sqrt2) t^1.5 sinw (1 + a1 tau + ...).
#   a1 = lim (Y3inv/((3/sqrt2)t^1.5 sinw) - 1)/tau
# ---------------------------------------------------------------
print("\nQ3/Q4: a1 = (ratio_Y3/(3/sqrt2) - 1)/tau  (the next-order RELATIVE coeff):")
a1s=[]; a1taus=[]
for m in [4,6,8,10,12,16,20,25,30]:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q))
    Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w)
    Y3invq = 3*((1-q**3)*Pk/(2*q**3)) - (1-q**(-3))*Se
    r=Y3invq/((3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw)
    a1=(r-1)/tau
    a1s.append(a1); a1taus.append(tau)
    print("  m=%2d tau=%.3e  ratio=%.10f  a1=%.6f" % (m, float(tau), float(r), float(a1)))
ca1=polyfit_const(a1taus, a1s, 3)
print("  a1 (LS limit) = %s   (compare 7/4=1.75, 9/5=1.8, etc.)" % mp.nstr(ca1[0],10))
# try to rationalize
for den in range(2,40):
    val=ca1[0]*den
    if abs(val-mp.nint(val))<mp.mpf('1e-4'):
        print("    candidate rational: %d/%d = %.6f" % (int(mp.nint(val)), den, float(mp.nint(val))/den))
