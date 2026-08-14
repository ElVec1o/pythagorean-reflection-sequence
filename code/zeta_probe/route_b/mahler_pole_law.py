"""
Locate MANY travel poles q_m (roots of Sigma_1(q)=1) on (0,1) robustly by sign-change
scanning in the w=sqrt(2/tau) variable, and examine the moduli pattern.

Mahler prediction: poles in |z|<1 sit at moduli |beta|^{1/k^j} for finitely many beta
(roots of a fixed polynomial Gamma) and j>=0. So the DISTINCT moduli accumulating at 1
form finitely many geometric sequences r_beta^{1/k^j} -> 1.
In particular: 1 - |q_m| should, for the Mahler family from a single beta, behave like
  1-|beta|^{1/k^j} ~ (-ln|beta|)/k^j  -> GEOMETRIC decay in j (ratio 1/k).
Test: do the V-poles' gaps (1-q_m) decay geometrically (Mahler) or like 1/m^2 (cosine model)?
"""
import mpmath as mp, math
mp.mp.dps=60

def Ak(k,tau):
    q=mp.e**(-tau); return 2*q/(1-q**(k+1))
def Ck(k,tau):
    q=mp.e**(-tau); return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigk(k,tau,dps):
    mp.mp.dps=dps
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(3000000):
        tot+=Ak(k+2*j,tau)*prod
        prod*=Ck(k+2*j,tau)
        if abs(prod)<mp.mpf(10)**(-(dps-15)) and j>40: break
    return tot
def dps_for(w): return int(float(w)/math.log(10))+55

def Sig1_w(w):
    tau=2/w**2
    return Sigk(1,tau,dps_for(w))

# scan w from 4 to 80, find sign changes of Sig1_w(w)-1
poles_w=[]
prev=None; pw=None
W=mp.mpf(4)
step=mp.mpf('0.05')
while W<mp.mpf(80):
    val=Sig1_w(W)-1
    s=int(mp.sign(val))
    if prev is not None and s!=0 and prev!=0 and s!=prev:
        lo,hi=pw,W; flo=prev
        for _ in range(80):
            m=(lo+hi)/2
            fm=int(mp.sign(Sig1_w(m)-1))
            if fm==flo or fm==0: lo=m
            else: hi=m
        wz=(lo+hi)/2
        poles_w.append(wz)
    if s!=0: prev=s; pw=W
    W+=step

print(f"Found {len(poles_w)} poles in w-window [4,80]")
qs=[mp.e**(-2/w**2) for w in poles_w]
print("\nq_m, 1-q_m, ratio of consecutive (1-q_m):")
prev_gap=None
for i,(w,q) in enumerate(zip(poles_w,qs)):
    gap=1-q
    r = prev_gap/gap if prev_gap else mp.mpf('nan')
    print(f"  m={i+1}: w={mp.nstr(w,8)}  q={mp.nstr(q,14)}  1-q={mp.nstr(gap,6)}  gap_ratio={mp.nstr(r,6)}")
    prev_gap=gap

# Mahler would force gap ratios -> 1/k (constant, e.g. 0.5 for k=2). 
# Cosine/natural-boundary model forces w_m ~ m*pi so tau~2/(m^2 pi^2), 1-q~tau~1/m^2,
# gap ratio ~ (m/(m+1))^2 -> 1 (NOT geometric). Let's see which.
print("\nIf Mahler (k=2): gap ratios -> 0.5 (geometric). If natural boundary: gap ratios -> 1.")
