"""
Audit the STEP-D narrative arithmetic precisely.

The script's STEP D comment writes:
   (2/3) cos W  = (2/3)(19/18) sqrt(tau/2) sin w   [using cosW = (19/18) sqrt(tau/2) sin w]
                = (2/3)(19/18)(1/sqrt2) sqrt(tau) sin w = (19/(27 sqrt2)) sqrt(tau) sin w
and then claims pref*Y3_lead = (2/(3 sqrt2)) sqrt(tau) sin w = 18/(27 sqrt2), and that the
mismatch 1/(27 sqrt2) sqrt(tau) sin w "is the O(tau^{3/2}) piece of P12".

ADVERSARIAL POINT 1 (dimensional): 1/(27 sqrt2) sqrt(tau) sin w is O(sqrt tau), NOT O(tau^{3/2}).
So the narrative's stated mismatch is dimensionally an O(sqrt tau) quantity, which CANNOT be
P12 = O(tau^{3/2}). If those two leading sqrt(tau) coefficients genuinely differed by 1/(27 sqrt2),
P12 would be O(sqrt tau), contradicting the proven gate. So the narrative arithmetic is WRONG.

ADVERSARIAL POINT 2: which of the two narrative inputs is the culprit?
 (a) Is pref*Y3_lead really 2/(3 sqrt2) sqrt(t) sinw?  -- test directly.
 (b) Is (2/3)*(2/3)Se ... wait, is (2/3)Se / (sqrt t sinw) -> 2/(3 sqrt2) or -> 19/(27 sqrt2)?
     If Se -> sqrt(tau/2) sinw (i.e. cosW const = 1, NOT 19/18 to leading sqrt-t order!), then
     (2/3)Se/(sqrt t sinw) -> (2/3)(1/sqrt2) = 2/(3 sqrt2) = 0.4714, matching A. The "19/18"
     must then be a HIGHER-order (relative O(tau)) effect, NOT the leading sqrt(t) coefficient.

So the real question: is the LEADING coefficient of cosW/( sqrt(tau/2) sinw) equal to 1 or 19/18?
The Richardson fit gave the *value at finite tau extrapolated to tau=0* = 19/18. But maybe that
limit 19/18 is itself NOT the leading-order coefficient in a sqrt(tau) expansion -- because cosW
is being normalized by sqrt(tau/2) sinw where sinw and the pole phase conspire. Let's separate:
write cosW directly and Se directly, normalized by sqrt(tau) (no sinw), and look at the actual
sqrt-tau coefficients. The cleanest invariant is B := (2/3)Se/(sqrt(tau) sinw).
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
taus=[]; Bvals=[]; Sevals=[]; cosWvals=[]
for m in ms:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q)); Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w); cosW=mp.cos(W)
    taus.append(tau)
    Bvals.append((mp.mpf(2)/3*Se)/(mp.sqrt(tau)*sinw))
    Sevals.append(Se/(mp.sqrt(tau)*sinw))          # Se/(sqrt t sinw) -> ?
    cosWvals.append(cosW/(mp.sqrt(tau)*sinw))        # cosW/(sqrt t sinw) -> ?

cB=polyfit(taus,Bvals,4)
cSe=polyfit(taus,Sevals,4)
cCos=polyfit(taus,cosWvals,4)
print("LEADING sqrt(tau) coefficients (normalized by sqrt(tau) sinw, NO sqrt(1/2) baked in):")
print("  Se/(sqrt t sinw)   -> %s   (1/sqrt2 = %s)" % (mp.nstr(cSe[0],12), mp.nstr(1/mp.sqrt(2),12)))
print("  cosW/(sqrt t sinw) -> %s   (1/sqrt2 = %s)" % (mp.nstr(cCos[0],12), mp.nstr(1/mp.sqrt(2),12)))
print("  (2/3)Se/(sqrt t sinw)->%s   (2/(3sqrt2)=%s)" % (mp.nstr(cB[0],12), mp.nstr(2/(3*mp.sqrt(2)),12)))
print()
print("So: Se/(sqrt(t) sinw) and cosW/(sqrt(t) sinw) BOTH -> 1/sqrt2 = 0.7071.")
print("The '19/18' appears ONLY when you normalize cosW by sqrt(tau/2) sinw = (1/sqrt2) sqrt(t) sinw,")
print("AND read the *extrapolated finite-tau* ratio. Check: (cosW/(sqrt(t) sinw)) / (1/sqrt2):")
print("  cCos[0]*sqrt2 = %s   (should be 1, NOT 19/18, if leading coeff is 1/sqrt2)"
      % mp.nstr(cCos[0]*mp.sqrt(2),12))
print()
print("RESOLUTION: cosW/(sqrt(tau/2) sinw) = sqrt2 * [cosW/(sqrt t sinw)]. Its tau->0 LIMIT:")
print("  = sqrt2 * cCos[0] = %s" % mp.nstr(cCos[0]*mp.sqrt(2),12))

# Now the decisive question: what does cosW/(sqrt(tau/2) sinw) ACTUALLY converge to?
cosWhalf=[]
for m in ms:
    q=POLES[m]; tau=-mp.log(q); setdps(tau)
    N=int(110/(1-q)); Pk,Se=cocycle(q,N)
    w=mp.sqrt(2/tau); W=w*mp.exp(-tau/2); sinw=mp.sin(w); cosW=mp.cos(W)
    cosWhalf.append(cosW/(mp.sqrt(tau/2)*sinw))
ch=polyfit(taus,cosWhalf,4)
print("\n  cosW/(sqrt(tau/2) sinw) LS-limit = %s ;  19/18 = %s ;  1 = 1"
      % (mp.nstr(ch[0],12), mp.nstr(mp.mpf(19)/18,12)))
print("  ===> the LIMIT is 19/18, but is 19/18 the *leading* term or does cosW have a sqrt(t)")
print("       leading whose coefficient (in the sqrt(t/2) normalization) is 19/18? They are the SAME")
print("       thing since sqrt(t/2) sinw ~ const*sqrt(t). So cosW ~ (19/18) sqrt(t/2) sinw, i.e.")
print("       cosW/(sqrt t sinw) -> (19/18)/sqrt2 = %s" % mp.nstr(mp.mpf(19)/18/mp.sqrt(2),12))
print("       BUT cCos[0] above = %s. Are these consistent?" % mp.nstr(cCos[0],12))
print("       (19/18)/sqrt2 = %s   vs cCos[0] = %s" % (mp.nstr(mp.mpf(19)/(18*mp.sqrt(2)),12), mp.nstr(cCos[0],12)))
