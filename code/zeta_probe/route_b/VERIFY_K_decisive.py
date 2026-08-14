"""
DECISIVE verification of the N=2 finite-order remainder ratio at travel poles.

The three Angle-3 verdicts DISAGREE on the load-bearing fact:
  rem3(tau) := (f - a1*tau - a2*tau^2)/tau^3,   f = Y3(1/q)/[(3/sqrt2) tau^{3/2} sin w] - 1
  - one says rem3 -> a3 = 1.74830 cleanly (m=3..79)
  - another says rem3 oscillates and GROWS: +10.7 (m=24), -12.6 (m=30), +28.8 (m=31)

This script settles it WITHOUT any integral / asymptotic: Y3(1/q) via the EXACT
algebraic cocycle identity, with a HARD precision-convergence gate per pole.

a1 = 2269/1296, a2 = 507266513/251942400, a3 = 2097873762713657/1199951262720000.
"""
import mpmath as mp

a1 = mp.mpf(2269)/1296
a2 = mp.mpf(507266513)/251942400
a3 = mp.mpf(2097873762713657)/1199951262720000

POLES=[l.strip() for l in open("poles.txt") if l.strip()]

def cocycle(q,N):
    x=mp.mpf(0); y=mp.mpf(1); X=mp.mpf(1); Y=mp.mpf(0); qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q; q2n=qn*qn; q3n=q2n*qn
        x,y,X,Y=(x*(1+2*q2n)-2*y*qn,2*x*q3n+y*(1-2*q2n),
                 X*(1+2*q2n)-2*Y*qn,2*X*q3n+Y*(1-2*q2n))
    return Y,y   # P12, Se

def eval_f(qstr, dps, Nfac):
    """Return f(tau) at the pole, exact cocycle Y3 identity. dps and Nfac control accuracy."""
    mp.mp.dps = dps
    q = mp.mpf(qstr)
    tau = -mp.log(q)
    w = mp.sqrt(2/tau)
    N = int(Nfac/(1-q))
    P12,Se = cocycle(q,N)
    Y3_1   = (1-q**3)*P12/(2*q**3)
    Y3_1oq = 3*Y3_1 - (1-q**(-3))*Se
    sinw = mp.sin(w)
    f = Y3_1oq/((3/mp.sqrt(2))*tau**mp.mpf('1.5')*sinw) - 1
    return tau, f, sinw

print("="*108)
print("rem3(tau) = (f - a1 tau - a2 tau^2)/tau^3   via EXACT cocycle identity (no integral, no asymptotics)")
print("a3 (target) = %s = %.7f" % (mp.nstr(a3,12), float(a3)))
print("Each pole: TWO independent (dps,Nfac) settings; PRINT both + agreement digits. rem3 trusted only if they AGREE.")
print("="*108)
print(f"{'m':>3} {'tau':>11} {'sin w':>11} {'rem3 (loP)':>16} {'rem3 (hiP)':>16} {'agree dig':>9} {'rem3-a3':>12}")

# sweep the disputed range thoroughly: m=3..40 plus a few beyond
ms = [3,4,5,6,7,8,10,12,13,14,16,18,19,20,21,22,24,25,26,27,30,31,35,39,45,55,65,79]
results=[]
for m in ms:
    if m >= len(POLES): continue
    qstr = POLES[m]
    q = mp.mpf(qstr)              # quick tau for sizing dps
    tau0 = float(-mp.log(q))
    w0 = (2/tau0)**0.5
    # dps must beat the O(sqrt tau) cancellation in f AND cocycle growth ~ e^{const/sqrt tau}
    base = 60 + int(2.2*w0)
    dpsLo = base
    dpsHi = base + int(0.9*w0) + 25
    NfacLo = 115
    NfacHi = 170
    try:
        tau, f1, sw1 = eval_f(qstr, dpsLo, NfacLo)
        _,   f2, sw2 = eval_f(qstr, dpsHi, NfacHi)
    except Exception as e:
        print(f"{m:>3}  ERROR {e}")
        continue
    # work at high precision for the subtraction
    mp.mp.dps = dpsHi
    tauh = -mp.log(mp.mpf(qstr))
    r1 = (f1 - a1*tauh - a2*tauh**2)/tauh**3
    r2 = (f2 - a1*tauh - a2*tauh**2)/tauh**3
    # agreement digits between the two settings (on f itself, the raw quantity)
    df = abs(f1-f2)
    if df == 0:
        agree = mp.mp.dps
    else:
        agree = -int(mp.log10(df/ (abs(f2)+mp.mpf(10)**(-mp.mp.dps))))
    results.append((m,float(tau),float(sw2),r2,agree))
    print(f"{m:>3} {float(tauh):>11.4e} {float(sw2):>11.3e} {mp.nstr(r1,9):>16} {mp.nstr(r2,9):>16} {agree:>9d} {mp.nstr(r2-a3,5):>12}")

print("\nINTERPRETATION:")
print("  If 'agree dig' is large (>~15) AND rem3(hiP)~rem3(loP), the value is REAL (precision-robust).")
print("  Verdict-1/2 claim rem3 -> 1.748 stable to m=79.  Verdict-3 claims blow-up to +28.8 at m=31.")
print("  The 'agree dig' column decides which: a blow-up with LOW agreement = precision artifact;")
print("  a blow-up with HIGH agreement = real and the K=1.77 claim is FALSE.")
